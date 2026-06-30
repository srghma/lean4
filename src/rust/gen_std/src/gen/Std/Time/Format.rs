// Lean compiler output
// Module: Std.Time.Format
// Imports: Std.Time.Notation.Spec Std.Time.Format.Basic Std.Time.Format.Basic
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_emod, lean_int_mod, lean_int_mul,
    lean_int_neg, lean_mk_thunk, lean_nat_mod, lean_nat_to_int, lean_string_append,
    lean_thunk_get_own,
};
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
static mut l_Std_Time_Formats_iso8601___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_iso8601___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_iso8601___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__2_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__3_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
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
static mut l_Std_Time_Formats_iso8601___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__7_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__8_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__10_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Time_Formats_iso8601___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__12_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 17,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__13_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__14_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Time_Formats_iso8601___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__15_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__16_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 18,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__17_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__18_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 19,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__19_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__20_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 27,
        },
        m_objs: [2 as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_iso8601___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__21_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__20_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__22_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__21_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__23_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__22_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__24_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__23_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__25_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__24_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__26_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__25_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__27_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__26_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__28_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__27_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__29_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__28_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__30_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__29_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__31_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__30_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__31_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__32_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__31_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_iso8601___closed__33_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__32_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_iso8601___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_iso8601___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_iso8601___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_iso8601: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_americanDate___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_americanDate___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_americanDate___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_americanDate___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_americanDate___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_americanDate: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_europeanDate___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_europeanDate___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_europeanDate___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_europeanDate___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_europeanDate___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_europeanDate___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_europeanDate___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_europeanDate___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_europeanDate___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_europeanDate: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_time12Hour___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 14,
        },
        m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_time12Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Time_Formats_time12Hour___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 13,
        },
        m_objs: [0 as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_time12Hour___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__5_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time12Hour___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time12Hour___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_time12Hour___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_time12Hour___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_time12Hour: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_time24Hour___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_time24Hour___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_time24Hour___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_time24Hour___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_time24Hour___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_time24Hour: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_dateTime24Hour___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
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
static mut l_Std_Time_Formats_dateTime24Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 20,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTime24Hour___closed__16_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_dateTime24Hour___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_dateTime24Hour___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_dateTime24Hour: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_dateTimeWithZone___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 29,
        },
        m_objs: [0 as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__1_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_dateTimeWithZone___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_dateTimeWithZone___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_dateTimeWithZone___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_dateTimeWithZone: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_Formats_leanTime24Hour___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanTime24Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanTime24Hour: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanTime24HourNoNanos: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__0_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__1_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__2_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__4_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24Hour___closed__5_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24Hour___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanDateTime24Hour___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTime24Hour: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTime24HourNoNanos: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 29,
    },
    m_objs: [2 as *mut leanh::LeanObject],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__1_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanDateTimeWithZone___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithZone: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithZoneNoNanos: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value:
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
    m_data: [91, 0],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 25,
    },
    m_objs: [1 as *mut leanh::LeanObject],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value:
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
    m_data: [93, 0],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__5_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__10_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__12_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__13_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__15_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__16_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__17_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__18_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithIdentifier: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_dateTime24Hour___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__3_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__9_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__10_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__11_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_leanDate___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_leanDate___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_leanDate___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_leanDate___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_leanDate___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_leanDate___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_leanDate: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_Formats_sqlDate: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_longDateFormat___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 10,
        },
        m_objs: [1 as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__2_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Time_Formats_longDateFormat___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 6,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__8_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_time24Hour___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__6_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_longDateFormat___closed__16_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_longDateFormat___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_longDateFormat___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_longDateFormat___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_longDateFormat: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Formats_ascTime___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 10,
        },
        m_objs: [0 as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_ascTime___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_Formats_ascTime___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__4_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_americanDate___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_ascTime___closed__16_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__15_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_ascTime___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_ascTime___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_ascTime___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_ascTime: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_rfc822___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 11,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_dateTimeWithZone___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__19_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__17_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__15_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__13_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__8_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__11_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_ascTime___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__12_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__14_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc822___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc822___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_rfc822___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_rfc822___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_rfc822: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Formats_rfc850___closed__0_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__9_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_iso8601___closed__9_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__4_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_longDateFormat___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__3_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Formats_rfc850___closed__5_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_rfc822___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_Formats_rfc850___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Formats_rfc850___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Formats_rfc850___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Formats_rfc850___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Formats_rfc850: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_TimeZone_fromTimeZone___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_fromTimeZone___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((24 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_fromTimeZone___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Formats_time12Hour___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_Formats_leanDateTimeWithZone___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_fromTimeZone___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_fromTimeZone___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_fromTimeZone___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_fromTimeZone___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value:
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
    m_fun: l_Std_Time_TimeZone_Offset_fromOffset___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 28,
    },
    m_objs: [2 as *mut leanh::LeanObject],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__2_value)
            as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_Offset_fromOffset___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_TimeZone_Offset_fromOffset___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_format___lam__0___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDate_format___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDate_format___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Time_PlainDate_format___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_format___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_format___closed__1_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Std_Time_PlainDate_format___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_format___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_fromAmericanDateString___closed__0_value:
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
    m_fun: l_Std_Time_PlainDate_fromAmericanDateString___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_fromAmericanDateString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_fromAmericanDateString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_fromSQLDateString___closed__0_value:
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
    m_fun: l_Std_Time_PlainDate_fromSQLDateString___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDate_fromSQLDateString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_fromSQLDateString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_toLeanDateString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value:
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
    m_data: [34, 41, 0],
};
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___lam__0___closed__3_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainDate_instRepr___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDate_instRepr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainDate_instRepr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_PlainTime_format___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainTime_format___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainTime_fromTime24Hour___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_PlainTime_fromTime24Hour___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_fromTime24Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_fromTime24Hour___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0_value:
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
    m_fun: l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainTime_fromTime12Hour___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainTime_fromTime12Hour___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_fromTime12Hour___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainTime_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainTime_toLeanTime24Hour as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Std_Time_PlainTime_instRepr___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainTime_instRepr___lam__0___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainTime_instRepr___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainTime_instRepr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainTime_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainTime_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainTime_instRepr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainTime_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_ZonedDateTime_format___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_ZonedDateTime_instToString___closed__0_value:
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
    m_fun: l_Std_Time_ZonedDateTime_toLeanDateTimeWithIdentifierString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_ZonedDateTime_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value:
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
    m_data: [122, 111, 110, 101, 100, 40, 34, 0],
};
static mut l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_ZonedDateTime_instRepr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_ZonedDateTime_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_ZonedDateTime_instRepr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_ZonedDateTime_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_fromAscTimeString___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_toAscTimeString___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDateTime_instToString___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_toLeanDateTimeString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value:
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
    m_data: [100, 97, 116, 101, 116, 105, 109, 101, 40, 34, 0],
};
static mut l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instRepr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instRepr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Std_Time_Formats_iso8601___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = l_Std_Time_DateFormat_enUS;
    v___x_1973_ = 0;
    v___x_1974_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1974_, 0, v___x_1972_);
    leanh::lean_ctor_set_uint8(
        v___x_1974_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1973_,
    );
    return v___x_1974_;
}
pub unsafe fn _init_l_Std_Time_Formats_iso8601___closed__34() -> *mut leanh::LeanObject {
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2050_ = l_Std_Time_Formats_iso8601___closed__33;
    v___x_2051_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2052_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2052_, 0, v___x_2051_);
    leanh::lean_ctor_set(v___x_2052_, 1, v___x_2050_);
    return v___x_2052_;
}
pub unsafe fn _init_l_Std_Time_Formats_iso8601() -> *mut leanh::LeanObject {
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2053_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__34),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__34_once),
        _init_l_Std_Time_Formats_iso8601___closed__34,
    );
    return v___x_2053_;
}
pub unsafe fn _init_l_Std_Time_Formats_americanDate___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = l_Std_Time_Formats_americanDate___closed__4;
    v___x_2070_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2071_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2071_, 0, v___x_2070_);
    leanh::lean_ctor_set(v___x_2071_, 1, v___x_2069_);
    return v___x_2071_;
}
pub unsafe fn _init_l_Std_Time_Formats_americanDate() -> *mut leanh::LeanObject {
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_americanDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_americanDate___closed__5_once),
        _init_l_Std_Time_Formats_americanDate___closed__5,
    );
    return v___x_2072_;
}
pub unsafe fn _init_l_Std_Time_Formats_europeanDate___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ = l_Std_Time_Formats_europeanDate___closed__2;
    v___x_2083_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2084_, 0, v___x_2083_);
    leanh::lean_ctor_set(v___x_2084_, 1, v___x_2082_);
    return v___x_2084_;
}
pub unsafe fn _init_l_Std_Time_Formats_europeanDate() -> *mut leanh::LeanObject {
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_europeanDate___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_europeanDate___closed__3_once),
        _init_l_Std_Time_Formats_europeanDate___closed__3,
    );
    return v___x_2085_;
}
pub unsafe fn _init_l_Std_Time_Formats_time12Hour___closed__13() -> *mut leanh::LeanObject {
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2118_ = l_Std_Time_Formats_time12Hour___closed__12;
    v___x_2119_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2120_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2120_, 0, v___x_2119_);
    leanh::lean_ctor_set(v___x_2120_, 1, v___x_2118_);
    return v___x_2120_;
}
pub unsafe fn _init_l_Std_Time_Formats_time12Hour() -> *mut leanh::LeanObject {
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time12Hour___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time12Hour___closed__13_once),
        _init_l_Std_Time_Formats_time12Hour___closed__13,
    );
    return v___x_2121_;
}
pub unsafe fn _init_l_Std_Time_Formats_time24Hour___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2137_ = l_Std_Time_Formats_time24Hour___closed__4;
    v___x_2138_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2139_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2139_, 0, v___x_2138_);
    leanh::lean_ctor_set(v___x_2139_, 1, v___x_2137_);
    return v___x_2139_;
}
pub unsafe fn _init_l_Std_Time_Formats_time24Hour() -> *mut leanh::LeanObject {
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2140_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5_once),
        _init_l_Std_Time_Formats_time24Hour___closed__5,
    );
    return v___x_2140_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTime24Hour___closed__17() -> *mut leanh::LeanObject
{
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2187_ = l_Std_Time_Formats_dateTime24Hour___closed__16;
    v___x_2188_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2189_, 0, v___x_2188_);
    leanh::lean_ctor_set(v___x_2189_, 1, v___x_2187_);
    return v___x_2189_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTime24Hour() -> *mut leanh::LeanObject {
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2190_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTime24Hour___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTime24Hour___closed__17_once),
        _init_l_Std_Time_Formats_dateTime24Hour___closed__17,
    );
    return v___x_2190_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTimeWithZone___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2237_ = l_Std_Time_Formats_dateTimeWithZone___closed__15;
    v___x_2238_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2239_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2239_, 0, v___x_2238_);
    leanh::lean_ctor_set(v___x_2239_, 1, v___x_2237_);
    return v___x_2239_;
}
pub unsafe fn _init_l_Std_Time_Formats_dateTimeWithZone() -> *mut leanh::LeanObject {
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2240_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTimeWithZone___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_dateTimeWithZone___closed__16_once),
        _init_l_Std_Time_Formats_dateTimeWithZone___closed__16,
    );
    return v___x_2240_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanTime24Hour___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = l_Std_Time_Formats_dateTime24Hour___closed__10;
    v___x_2242_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2243_, 0, v___x_2242_);
    leanh::lean_ctor_set(v___x_2243_, 1, v___x_2241_);
    return v___x_2243_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanTime24Hour() -> *mut leanh::LeanObject {
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2244_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanTime24Hour___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanTime24Hour___closed__0_once),
        _init_l_Std_Time_Formats_leanTime24Hour___closed__0,
    );
    return v___x_2244_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanTime24HourNoNanos() -> *mut leanh::LeanObject {
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2245_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_time24Hour___closed__5_once),
        _init_l_Std_Time_Formats_time24Hour___closed__5,
    );
    return v___x_2245_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24Hour___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Std_Time_Formats_leanDateTime24Hour___closed__5;
    v___x_2265_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2266_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2266_, 0, v___x_2265_);
    leanh::lean_ctor_set(v___x_2266_, 1, v___x_2264_);
    return v___x_2266_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24Hour() -> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24Hour___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24Hour___closed__6_once),
        _init_l_Std_Time_Formats_leanDateTime24Hour___closed__6,
    );
    return v___x_2267_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__5;
    v___x_2287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2288_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2288_, 0, v___x_2287_);
    leanh::lean_ctor_set(v___x_2288_, 1, v___x_2286_);
    return v___x_2288_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTime24HourNoNanos() -> *mut leanh::LeanObject
{
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2289_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6_once),
        _init_l_Std_Time_Formats_leanDateTime24HourNoNanos___closed__6,
    );
    return v___x_2289_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZone___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Std_Time_Formats_leanDateTimeWithZone___closed__15;
    v___x_2337_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2338_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2338_, 0, v___x_2337_);
    leanh::lean_ctor_set(v___x_2338_, 1, v___x_2336_);
    return v___x_2338_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZone() -> *mut leanh::LeanObject {
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2339_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZone___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZone___closed__16_once),
        _init_l_Std_Time_Formats_leanDateTimeWithZone___closed__16,
    );
    return v___x_2339_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2373_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__10;
    v___x_2374_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2375_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2375_, 0, v___x_2374_);
    leanh::lean_ctor_set(v___x_2375_, 1, v___x_2373_);
    return v___x_2375_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos() -> *mut leanh::LeanObject
{
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2376_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11_once),
        _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos___closed__11,
    );
    return v___x_2376_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__19;
    v___x_2430_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2431_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2431_, 0, v___x_2430_);
    leanh::lean_ctor_set(v___x_2431_, 1, v___x_2429_);
    return v___x_2431_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifier() -> *mut leanh::LeanObject
{
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2432_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20_once),
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifier___closed__20,
    );
    return v___x_2432_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__12;
    v___x_2473_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2474_, 0, v___x_2473_);
    leanh::lean_ctor_set(v___x_2474_, 1, v___x_2472_);
    return v___x_2474_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos()
-> *mut leanh::LeanObject {
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2475_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13),
        core::ptr::addr_of_mut!(
            l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13_once
        ),
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos___closed__13,
    );
    return v___x_2475_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDate___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2491_ = l_Std_Time_Formats_leanDate___closed__4;
    v___x_2492_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2493_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2493_, 0, v___x_2492_);
    leanh::lean_ctor_set(v___x_2493_, 1, v___x_2491_);
    return v___x_2493_;
}
pub unsafe fn _init_l_Std_Time_Formats_leanDate() -> *mut leanh::LeanObject {
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5_once),
        _init_l_Std_Time_Formats_leanDate___closed__5,
    );
    return v___x_2494_;
}
pub unsafe fn _init_l_Std_Time_Formats_sqlDate() -> *mut leanh::LeanObject {
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2495_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_leanDate___closed__5_once),
        _init_l_Std_Time_Formats_leanDate___closed__5,
    );
    return v___x_2495_;
}
pub unsafe fn _init_l_Std_Time_Formats_longDateFormat___closed__17() -> *mut leanh::LeanObject
{
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2538_ = l_Std_Time_Formats_longDateFormat___closed__16;
    v___x_2539_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2540_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2540_, 0, v___x_2539_);
    leanh::lean_ctor_set(v___x_2540_, 1, v___x_2538_);
    return v___x_2540_;
}
pub unsafe fn _init_l_Std_Time_Formats_longDateFormat() -> *mut leanh::LeanObject {
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_longDateFormat___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_longDateFormat___closed__17_once),
        _init_l_Std_Time_Formats_longDateFormat___closed__17,
    );
    return v___x_2541_;
}
pub unsafe fn _init_l_Std_Time_Formats_ascTime___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2589_ = l_Std_Time_Formats_ascTime___closed__16;
    v___x_2590_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2591_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2591_, 0, v___x_2590_);
    leanh::lean_ctor_set(v___x_2591_, 1, v___x_2589_);
    return v___x_2591_;
}
pub unsafe fn _init_l_Std_Time_Formats_ascTime() -> *mut leanh::LeanObject {
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2592_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_ascTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_ascTime___closed__17_once),
        _init_l_Std_Time_Formats_ascTime___closed__17,
    );
    return v___x_2592_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc822___closed__16() -> *mut leanh::LeanObject {
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2639_ = l_Std_Time_Formats_rfc822___closed__15;
    v___x_2640_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2641_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2641_, 0, v___x_2640_);
    leanh::lean_ctor_set(v___x_2641_, 1, v___x_2639_);
    return v___x_2641_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc822() -> *mut leanh::LeanObject {
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2642_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc822___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc822___closed__16_once),
        _init_l_Std_Time_Formats_rfc822___closed__16,
    );
    return v___x_2642_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc850___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2661_ = l_Std_Time_Formats_rfc850___closed__5;
    v___x_2662_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v___x_2663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2663_, 0, v___x_2662_);
    leanh::lean_ctor_set(v___x_2663_, 1, v___x_2661_);
    return v___x_2663_;
}
pub unsafe fn _init_l_Std_Time_Formats_rfc850() -> *mut leanh::LeanObject {
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2664_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc850___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_rfc850___closed__6_once),
        _init_l_Std_Time_Formats_rfc850___closed__6,
    );
    return v___x_2664_;
}
pub unsafe fn l_Std_Time_TimeZone_fromTimeZone___lam__0(
    mut v___x_2665_: u8,
    mut v_id_2666_: *mut leanh::LeanObject,
    mut v_off_2667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2668_: u8 = 0;
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2668_ = 1;
    leanh::lean_inc(v_off_2667_);
    v___x_2669_ = l_Std_Time_TimeZone_Offset_toIsoString(v_off_2667_, v___x_2668_);
    v___x_2670_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_2670_, 0, v_off_2667_);
    leanh::lean_ctor_set(v___x_2670_, 1, v_id_2666_);
    leanh::lean_ctor_set(v___x_2670_, 2, v___x_2669_);
    leanh::lean_ctor_set_uint8(
        v___x_2670_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_2665_,
    );
    v___x_2671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2671_, 0, v___x_2670_);
    return v___x_2671_;
}
pub unsafe fn l_Std_Time_TimeZone_fromTimeZone___lam__0___boxed(
    mut v___x_2672_: *mut leanh::LeanObject,
    mut v_id_2673_: *mut leanh::LeanObject,
    mut v_off_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_30__boxed_2675_: u8 = 0;
    let mut v_res_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_30__boxed_2675_ = (leanh::lean_unbox(v___x_2672_) as u8);
    v_res_2676_ =
        l_Std_Time_TimeZone_fromTimeZone___lam__0(v___x_30__boxed_2675_, v_id_2673_, v_off_2674_);
    return v_res_2676_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_fromTimeZone___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2688_ = l_Std_Time_TimeZone_fromTimeZone___closed__3;
    v___x_2689_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_spec_2690_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_spec_2690_, 0, v___x_2689_);
    leanh::lean_ctor_set(v_spec_2690_, 1, v___x_2688_);
    return v_spec_2690_;
}
pub unsafe fn l_Std_Time_TimeZone_fromTimeZone(
    mut v_input_2691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2692_ = l_Std_Time_TimeZone_fromTimeZone___closed__0;
    v_spec_2693_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_fromTimeZone___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_fromTimeZone___closed__4_once),
        _init_l_Std_Time_TimeZone_fromTimeZone___closed__4,
    );
    v___x_2694_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_2693_, v___f_2692_, v_input_2691_);
    return v___x_2694_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_fromOffset___lam__0(
    mut v_val_2695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2696_, 0, v_val_2695_);
    return v___x_2696_;
}
pub unsafe fn _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2705_ = l_Std_Time_TimeZone_Offset_fromOffset___closed__3;
    v___x_2706_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_spec_2707_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_spec_2707_, 0, v___x_2706_);
    leanh::lean_ctor_set(v_spec_2707_, 1, v___x_2705_);
    return v_spec_2707_;
}
pub unsafe fn l_Std_Time_TimeZone_Offset_fromOffset(
    mut v_input_2708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_spec_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2709_ = l_Std_Time_TimeZone_Offset_fromOffset___closed__0;
    v_spec_2710_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_fromOffset___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_TimeZone_Offset_fromOffset___closed__4_once),
        _init_l_Std_Time_TimeZone_Offset_fromOffset___closed__4,
    );
    v___x_2711_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v_spec_2710_, v___f_2709_, v_input_2708_);
    return v___x_2711_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = leanh::lean_unsigned_to_nat(4);
    v___x_2713_ = lean_nat_to_int(v___x_2712_);
    return v___x_2713_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2714_ = leanh::lean_unsigned_to_nat(0);
    v___x_2715_ = lean_nat_to_int(v___x_2714_);
    return v___x_2715_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = leanh::lean_unsigned_to_nat(400);
    v___x_2717_ = lean_nat_to_int(v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_format___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2718_ = leanh::lean_unsigned_to_nat(100);
    v___x_2719_ = lean_nat_to_int(v___x_2718_);
    return v___x_2719_;
}
pub unsafe fn l_Std_Time_PlainDate_format___lam__0(
    mut v_date_2720_: *mut leanh::LeanObject,
    mut v_locale_2721_: *mut leanh::LeanObject,
    mut v_x_2722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2724_: u8 = 0;
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: u8 = 0;
    let mut v___x_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v_year_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut v_unused_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v_year_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut v_unused_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2753_: u8 = 0;
    let mut v_firstDayOfWeek_2754_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut v_unused_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: u8 = 0;
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2780_: u8 = 0;
    let mut v_unused_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v_firstDayOfWeek_2785_: u8 = 0;
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2790_: u8 = 0;
    let mut v_unused_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2794_: u8 = 0;
    let mut v_firstDayOfWeek_2795_: u8 = 0;
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2800_: u8 = 0;
    let mut v_unused_2801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v_month_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2809_: u8 = 0;
    let mut v_unused_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v_day_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2818_: u8 = 0;
    let mut v_unused_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v___x_2826_: u8 = 0;
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v_unused_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut v_unused_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2722_) {
                0 => {
                    leanh::lean_dec_ref_known(v_x_2722_, 0);
                    v_year_2729_ = leanh::lean_ctor_get(v_date_2720_, 0);
                    leanh::lean_inc(v_year_2729_);
                    leanh::lean_dec_ref(v_date_2720_);
                    v___x_2730_ = l_Std_Time_Year_Offset_era(v_year_2729_);
                    leanh::lean_dec(v_year_2729_);
                    v___x_2731_ = leanh::lean_box((v___x_2730_) as usize);
                    v___x_2732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2732_, 0, v___x_2731_);
                    return v___x_2732_;
                }
                1 => {
                    v_isSharedCheck_2740_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2740_ == 0 {
                        v_unused_2741_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2741_);
                        v___x_2734_ = v_x_2722_;
                        v_isShared_2735_ = v_isSharedCheck_2740_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2734_ = leanh::lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2740_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_isSharedCheck_2749_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2749_ == 0 {
                        v_unused_2750_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2750_);
                        v___x_2743_ = v_x_2722_;
                        v_isShared_2744_ = v_isSharedCheck_2749_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2743_ = leanh::lean_box(0);
                        v_isShared_2744_ = v_isSharedCheck_2749_;
                        state = 4;
                        continue;
                    }
                }
                3 => {
                    v_isSharedCheck_2759_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v_unused_2760_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2760_);
                        v___x_2752_ = v_x_2722_;
                        v_isShared_2753_ = v_isSharedCheck_2759_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2752_ = leanh::lean_box(0);
                        v_isShared_2753_ = v_isSharedCheck_2759_;
                        state = 6;
                        continue;
                    }
                }
                4 => {
                    leanh::lean_dec_ref_known(v_x_2722_, 1);
                    v_year_2761_ = leanh::lean_ctor_get(v_date_2720_, 0);
                    v___x_2762_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__0_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                    );
                    v___x_2763_ = lean_int_mod(v_year_2761_, v___x_2762_);
                    v___x_2764_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__1_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                    );
                    v___x_2769_ = lean_int_dec_eq(v___x_2763_, v___x_2764_);
                    leanh::lean_dec(v___x_2763_);
                    if v___x_2769_ == 0 {
                        v___y_2724_ = v___x_2769_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2770_ = leanh::lean_obj_once(
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
                        leanh::lean_dec(v___x_2771_);
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
                    v_isSharedCheck_2780_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2780_ == 0 {
                        v_unused_2781_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2781_);
                        v___x_2774_ = v_x_2722_;
                        v_isShared_2775_ = v_isSharedCheck_2780_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2774_ = leanh::lean_box(0);
                        v_isShared_2775_ = v_isSharedCheck_2780_;
                        state = 9;
                        continue;
                    }
                }
                8 => {
                    v_isSharedCheck_2790_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2790_ == 0 {
                        v_unused_2791_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2791_);
                        v___x_2783_ = v_x_2722_;
                        v_isShared_2784_ = v_isSharedCheck_2790_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2783_ = leanh::lean_box(0);
                        v_isShared_2784_ = v_isSharedCheck_2790_;
                        state = 11;
                        continue;
                    }
                }
                9 => {
                    v_isSharedCheck_2800_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2800_ == 0 {
                        v_unused_2801_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2801_);
                        v___x_2793_ = v_x_2722_;
                        v_isShared_2794_ = v_isSharedCheck_2800_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2793_ = leanh::lean_box(0);
                        v_isShared_2794_ = v_isSharedCheck_2800_;
                        state = 13;
                        continue;
                    }
                }
                5 => {
                    v_isSharedCheck_2809_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2809_ == 0 {
                        v_unused_2810_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2810_);
                        v___x_2803_ = v_x_2722_;
                        v_isShared_2804_ = v_isSharedCheck_2809_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2803_ = leanh::lean_box(0);
                        v_isShared_2804_ = v_isSharedCheck_2809_;
                        state = 15;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_2818_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2818_ == 0 {
                        v_unused_2819_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2819_);
                        v___x_2812_ = v_x_2722_;
                        v_isShared_2813_ = v_isSharedCheck_2818_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2812_ = leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2818_;
                        state = 17;
                        continue;
                    }
                }
                10 => {
                    leanh::lean_dec_ref_known(v_x_2722_, 0);
                    v___x_2820_ = l_Std_Time_PlainDate_weekday(v_date_2720_);
                    v___x_2821_ = leanh::lean_box((v___x_2820_) as usize);
                    v___x_2822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2822_, 0, v___x_2821_);
                    return v___x_2822_;
                }
                11 => {
                    v_isSharedCheck_2831_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2831_ == 0 {
                        v_unused_2832_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2832_);
                        v___x_2824_ = v_x_2722_;
                        v_isShared_2825_ = v_isSharedCheck_2831_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2824_ = leanh::lean_box(0);
                        v_isShared_2825_ = v_isSharedCheck_2831_;
                        state = 19;
                        continue;
                    }
                }
                12 => {
                    v_isSharedCheck_2840_ = (!leanh::lean_is_exclusive(v_x_2722_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v_unused_2841_ = leanh::lean_ctor_get(v_x_2722_, 0);
                        leanh::lean_dec(v_unused_2841_);
                        v___x_2834_ = v_x_2722_;
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2722_);
                        v___x_2834_ = leanh::lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 21;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_2722_);
                    leanh::lean_dec_ref(v_date_2720_);
                    v___x_2842_ = leanh::lean_box(0);
                    return v___x_2842_;
                }
            },
            1 => {
                v___x_2725_ = l_Std_Time_PlainDate_dayOfYear(v_date_2720_);
                leanh::lean_dec_ref(v_date_2720_);
                v___x_2726_ = leanh::lean_box((v___y_2724_) as usize);
                v___x_2727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2727_, 0, v___x_2726_);
                leanh::lean_ctor_set(v___x_2727_, 1, v___x_2725_);
                v___x_2728_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2728_, 0, v___x_2727_);
                return v___x_2728_;
            }
            2 => {
                v_year_2736_ = leanh::lean_ctor_get(v_date_2720_, 0);
                leanh::lean_inc(v_year_2736_);
                leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2735_ == 0 {
                    leanh::lean_ctor_set(v___x_2734_, 0, v_year_2736_);
                    v___x_2738_ = v___x_2734_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_year_2736_);
                    v___x_2738_ = v_reuseFailAlloc_2739_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2738_;
            }
            4 => {
                v_year_2745_ = leanh::lean_ctor_get(v_date_2720_, 0);
                leanh::lean_inc(v_year_2745_);
                leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2744_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2743_, 1);
                    leanh::lean_ctor_set(v___x_2743_, 0, v_year_2745_);
                    v___x_2747_ = v___x_2743_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_year_2745_);
                    v___x_2747_ = v_reuseFailAlloc_2748_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2747_;
            }
            6 => {
                v_firstDayOfWeek_2754_ = leanh::lean_ctor_get_uint8(
                    v_locale_2721_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_2755_ = l_Std_Time_PlainDate_weekYear(v_date_2720_, v_firstDayOfWeek_2754_);
                if v_isShared_2753_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2752_, 1);
                    leanh::lean_ctor_set(v___x_2752_, 0, v___x_2755_);
                    v___x_2757_ = v___x_2752_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
                    v___x_2757_ = v_reuseFailAlloc_2758_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2757_;
            }
            8 => {
                v___x_2766_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_2767_ = lean_int_mod(v_year_2761_, v___x_2766_);
                v___x_2768_ = lean_int_dec_eq(v___x_2767_, v___x_2764_);
                leanh::lean_dec(v___x_2767_);
                v___y_2724_ = v___x_2768_;
                state = 1;
                continue;
            }
            9 => {
                v___x_2776_ = l_Std_Time_PlainDate_quarter(v_date_2720_);
                leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2774_, 1);
                    leanh::lean_ctor_set(v___x_2774_, 0, v___x_2776_);
                    v___x_2778_ = v___x_2774_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2779_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2779_, 0, v___x_2776_);
                    v___x_2778_ = v_reuseFailAlloc_2779_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2778_;
            }
            11 => {
                v_firstDayOfWeek_2785_ = leanh::lean_ctor_get_uint8(
                    v_locale_2721_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_2786_ = l_Std_Time_PlainDate_weekOfYear(v_date_2720_, v_firstDayOfWeek_2785_);
                if v_isShared_2784_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2783_, 1);
                    leanh::lean_ctor_set(v___x_2783_, 0, v___x_2786_);
                    v___x_2788_ = v___x_2783_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
                    v___x_2788_ = v_reuseFailAlloc_2789_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2788_;
            }
            13 => {
                v_firstDayOfWeek_2795_ = leanh::lean_ctor_get_uint8(
                    v_locale_2721_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_2796_ =
                    l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2720_, v_firstDayOfWeek_2795_);
                if v_isShared_2794_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2793_, 1);
                    leanh::lean_ctor_set(v___x_2793_, 0, v___x_2796_);
                    v___x_2798_ = v___x_2793_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2799_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
                    v___x_2798_ = v_reuseFailAlloc_2799_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2798_;
            }
            15 => {
                v_month_2805_ = leanh::lean_ctor_get(v_date_2720_, 1);
                leanh::lean_inc(v_month_2805_);
                leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2804_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2803_, 1);
                    leanh::lean_ctor_set(v___x_2803_, 0, v_month_2805_);
                    v___x_2807_ = v___x_2803_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_month_2805_);
                    v___x_2807_ = v_reuseFailAlloc_2808_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2807_;
            }
            17 => {
                v_day_2814_ = leanh::lean_ctor_get(v_date_2720_, 2);
                leanh::lean_inc(v_day_2814_);
                leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2813_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2812_, 1);
                    leanh::lean_ctor_set(v___x_2812_, 0, v_day_2814_);
                    v___x_2816_ = v___x_2812_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2817_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_day_2814_);
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
                v___x_2827_ = leanh::lean_box((v___x_2826_) as usize);
                if v_isShared_2825_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2824_, 1);
                    leanh::lean_ctor_set(v___x_2824_, 0, v___x_2827_);
                    v___x_2829_ = v___x_2824_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
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
                leanh::lean_dec_ref(v_date_2720_);
                if v_isShared_2835_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2834_, 1);
                    leanh::lean_ctor_set(v___x_2834_, 0, v___x_2836_);
                    v___x_2838_ = v___x_2834_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
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
    mut v_date_2843_: *mut leanh::LeanObject,
    mut v_locale_2844_: *mut leanh::LeanObject,
    mut v_x_2845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2846_ = l_Std_Time_PlainDate_format___lam__0(v_date_2843_, v_locale_2844_, v_x_2845_);
    leanh::lean_dec_ref(v_locale_2844_);
    return v_res_2846_;
}
pub unsafe fn l_Std_Time_PlainDate_format(
    mut v_date_2849_: *mut leanh::LeanObject,
    mut v_format_2850_: *mut leanh::LeanObject,
    mut v_locale_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2852_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_2853_ = l_Std_Time_GenericFormat_spec___redArg(v_format_2850_, v___x_2852_);
    if leanh::lean_obj_tag(v_format_2853_) == 0 {
        let mut v_a_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_locale_2851_);
        leanh::lean_dec_ref(v_date_2849_);
        v_a_2854_ = leanh::lean_ctor_get(v_format_2853_, 0);
        leanh::lean_inc(v_a_2854_);
        leanh::lean_dec_ref_known(v_format_2853_, 1);
        v___x_2855_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_2856_ = lean_string_append(v___x_2855_, v_a_2854_);
        leanh::lean_dec(v_a_2854_);
        return v___x_2856_;
    } else {
        let mut v_a_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2857_ = leanh::lean_ctor_get(v_format_2853_, 0);
        leanh::lean_inc(v_a_2857_);
        leanh::lean_dec_ref_known(v_format_2853_, 1);
        v___f_2858_ = leanh::lean_alloc_closure(
            l_Std_Time_PlainDate_format___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_2858_, 0, v_date_2849_);
        leanh::lean_closure_set(v___f_2858_, 1, v_locale_2851_);
        v_res_2859_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_2857_, v___f_2858_);
        if leanh::lean_obj_tag(v_res_2859_) == 0 {
            let mut v___x_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2860_ = l_Std_Time_PlainDate_format___closed__1;
            return v___x_2860_;
        } else {
            let mut v_val_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2861_ = leanh::lean_ctor_get(v_res_2859_, 0);
            leanh::lean_inc(v_val_2861_);
            leanh::lean_dec_ref_known(v_res_2859_, 1);
            return v_val_2861_;
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_fromAmericanDateString___lam__0(
    mut v_m_2862_: *mut leanh::LeanObject,
    mut v_d_2863_: *mut leanh::LeanObject,
    mut v_y_2864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2866_: u8 = 0;
    let mut v___x_2867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: u8 = 0;
    let mut v___x_2879_: u8 = 0;
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2872_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_2873_ = lean_int_mod(v_y_2864_, v___x_2872_);
                v___x_2874_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_2879_ = lean_int_dec_eq(v___x_2873_, v___x_2874_);
                leanh::lean_dec(v___x_2873_);
                if v___x_2879_ == 0 {
                    v___y_2866_ = v___x_2879_;
                    state = 1;
                    continue;
                } else {
                    v___x_2880_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_2881_ = lean_int_mod(v_y_2864_, v___x_2880_);
                    v___x_2882_ = lean_int_dec_eq(v___x_2881_, v___x_2874_);
                    leanh::lean_dec(v___x_2881_);
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
                leanh::lean_dec(v___x_2867_);
                if v___x_2868_ == 0 {
                    leanh::lean_dec(v_y_2864_);
                    leanh::lean_dec(v_d_2863_);
                    leanh::lean_dec(v_m_2862_);
                    v___x_2869_ = leanh::lean_box(0);
                    return v___x_2869_;
                } else {
                    v___x_2870_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2870_, 0, v_y_2864_);
                    leanh::lean_ctor_set(v___x_2870_, 1, v_m_2862_);
                    leanh::lean_ctor_set(v___x_2870_, 2, v_d_2863_);
                    v___x_2871_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2871_, 0, v___x_2870_);
                    return v___x_2871_;
                }
            }
            2 => {
                v___x_2876_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_2877_ = lean_int_mod(v_y_2864_, v___x_2876_);
                v___x_2878_ = lean_int_dec_eq(v___x_2877_, v___x_2874_);
                leanh::lean_dec(v___x_2877_);
                v___y_2866_ = v___x_2878_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_fromAmericanDateString(
    mut v_input_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2885_ = l_Std_Time_PlainDate_fromAmericanDateString___closed__0;
    v___x_2886_ = l_Std_Time_Formats_americanDate;
    v___x_2887_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_2886_, v___f_2885_, v_input_2884_);
    return v___x_2887_;
}
pub unsafe fn l_Std_Time_PlainDate_toAmericanDateString(
    mut v_input_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_year_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_year_2889_ = leanh::lean_ctor_get(v_input_2888_, 0);
    leanh::lean_inc(v_year_2889_);
    v_month_2890_ = leanh::lean_ctor_get(v_input_2888_, 1);
    leanh::lean_inc(v_month_2890_);
    v_day_2891_ = leanh::lean_ctor_get(v_input_2888_, 2);
    leanh::lean_inc(v_day_2891_);
    leanh::lean_dec_ref(v_input_2888_);
    v___x_2892_ = l_Std_Time_Formats_americanDate;
    v___x_6__overap_2893_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2892_);
    v___x_2894_ = leanh::lean_apply_3(
        v___x_6__overap_2893_,
        v_month_2890_,
        v_day_2891_,
        v_year_2889_,
    );
    return v___x_2894_;
}
pub unsafe fn l_Std_Time_PlainDate_fromSQLDateString___lam__0(
    mut v___y_2895_: *mut leanh::LeanObject,
    mut v___y_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2899_: u8 = 0;
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: u8 = 0;
    let mut v___x_2912_: u8 = 0;
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2905_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_2906_ = lean_int_mod(v___y_2895_, v___x_2905_);
                v___x_2907_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_2912_ = lean_int_dec_eq(v___x_2906_, v___x_2907_);
                leanh::lean_dec(v___x_2906_);
                if v___x_2912_ == 0 {
                    v___y_2899_ = v___x_2912_;
                    state = 1;
                    continue;
                } else {
                    v___x_2913_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_2914_ = lean_int_mod(v___y_2895_, v___x_2913_);
                    v___x_2915_ = lean_int_dec_eq(v___x_2914_, v___x_2907_);
                    leanh::lean_dec(v___x_2914_);
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
                leanh::lean_dec(v___x_2900_);
                if v___x_2901_ == 0 {
                    leanh::lean_dec(v___y_2897_);
                    leanh::lean_dec(v___y_2896_);
                    leanh::lean_dec(v___y_2895_);
                    v___x_2902_ = leanh::lean_box(0);
                    return v___x_2902_;
                } else {
                    v___x_2903_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2903_, 0, v___y_2895_);
                    leanh::lean_ctor_set(v___x_2903_, 1, v___y_2896_);
                    leanh::lean_ctor_set(v___x_2903_, 2, v___y_2897_);
                    v___x_2904_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2904_, 0, v___x_2903_);
                    return v___x_2904_;
                }
            }
            2 => {
                v___x_2909_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_2910_ = lean_int_mod(v___y_2895_, v___x_2909_);
                v___x_2911_ = lean_int_dec_eq(v___x_2910_, v___x_2907_);
                leanh::lean_dec(v___x_2910_);
                v___y_2899_ = v___x_2911_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_fromSQLDateString(
    mut v_input_2917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2918_ = l_Std_Time_PlainDate_fromSQLDateString___closed__0;
    v___x_2919_ = l_Std_Time_Formats_sqlDate;
    v___x_2920_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_2919_, v___f_2918_, v_input_2917_);
    return v___x_2920_;
}
pub unsafe fn l_Std_Time_PlainDate_toSQLDateString(
    mut v_input_2921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_year_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_year_2922_ = leanh::lean_ctor_get(v_input_2921_, 0);
    leanh::lean_inc(v_year_2922_);
    v_month_2923_ = leanh::lean_ctor_get(v_input_2921_, 1);
    leanh::lean_inc(v_month_2923_);
    v_day_2924_ = leanh::lean_ctor_get(v_input_2921_, 2);
    leanh::lean_inc(v_day_2924_);
    leanh::lean_dec_ref(v_input_2921_);
    v___x_2925_ = l_Std_Time_Formats_sqlDate;
    v___x_6__overap_2926_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2925_);
    v___x_2927_ = leanh::lean_apply_3(
        v___x_6__overap_2926_,
        v_year_2922_,
        v_month_2923_,
        v_day_2924_,
    );
    return v___x_2927_;
}
pub unsafe fn l_Std_Time_PlainDate_fromLeanDateString(
    mut v_input_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2929_ = l_Std_Time_PlainDate_fromSQLDateString___closed__0;
    v___x_2930_ = l_Std_Time_Formats_leanDate;
    v___x_2931_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_2930_, v___f_2929_, v_input_2928_);
    return v___x_2931_;
}
pub unsafe fn l_Std_Time_PlainDate_toLeanDateString(
    mut v_input_2932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_year_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_year_2933_ = leanh::lean_ctor_get(v_input_2932_, 0);
    leanh::lean_inc(v_year_2933_);
    v_month_2934_ = leanh::lean_ctor_get(v_input_2932_, 1);
    leanh::lean_inc(v_month_2934_);
    v_day_2935_ = leanh::lean_ctor_get(v_input_2932_, 2);
    leanh::lean_inc(v_day_2935_);
    leanh::lean_dec_ref(v_input_2932_);
    v___x_2936_ = l_Std_Time_Formats_leanDate;
    v___x_6__overap_2937_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_2936_);
    v___x_2938_ = leanh::lean_apply_3(
        v___x_6__overap_2937_,
        v_year_2933_,
        v_month_2934_,
        v_day_2935_,
    );
    return v___x_2938_;
}
pub unsafe fn l_Std_Time_PlainDate_parse(
    mut v_input_2939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_input_2939_);
    v___x_2940_ = l_Std_Time_PlainDate_fromAmericanDateString(v_input_2939_);
    if leanh::lean_obj_tag(v___x_2940_) == 0 {
        let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_2940_, 1);
        v___x_2941_ = l_Std_Time_PlainDate_fromSQLDateString(v_input_2939_);
        return v___x_2941_;
    } else {
        leanh::lean_dec_ref(v_input_2939_);
        return v___x_2940_;
    }
}
pub unsafe fn l_Std_Time_PlainDate_instRepr___lam__0(
    mut v_data_2950_: *mut leanh::LeanObject,
    mut v___y_2951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2952_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__1;
    v___x_2953_ = l_Std_Time_PlainDate_toLeanDateString(v_data_2950_);
    v___x_2954_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2954_, 0, v___x_2953_);
    v___x_2955_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2955_, 0, v___x_2952_);
    leanh::lean_ctor_set(v___x_2955_, 1, v___x_2954_);
    v___x_2956_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_2957_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2957_, 0, v___x_2955_);
    leanh::lean_ctor_set(v___x_2957_, 1, v___x_2956_);
    v___x_2958_ = l_Repr_addAppParen(v___x_2957_, v___y_2951_);
    return v___x_2958_;
}
pub unsafe fn l_Std_Time_PlainDate_instRepr___lam__0___boxed(
    mut v_data_2959_: *mut leanh::LeanObject,
    mut v___y_2960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2961_ = l_Std_Time_PlainDate_instRepr___lam__0(v_data_2959_, v___y_2960_);
    leanh::lean_dec(v___y_2960_);
    return v_res_2961_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_format___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2964_ = leanh::lean_unsigned_to_nat(12);
    v___x_2965_ = lean_nat_to_int(v___x_2964_);
    return v___x_2965_;
}
pub unsafe fn l_Std_Time_PlainTime_format___lam__0(
    mut v_time_2966_: *mut leanh::LeanObject,
    mut v_x_2967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2970_: u8 = 0;
    let mut v_hour_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2975_: u8 = 0;
    let mut v_unused_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v_hour_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_unused_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2989_: u8 = 0;
    let mut v_minute_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v_unused_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v_nanosecond_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v_unused_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3007_: u8 = 0;
    let mut v_second_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_unused_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3020_: u8 = 0;
    let mut v_hour_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3026_: u8 = 0;
    let mut v_unused_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v_hour_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v_nanosecond_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut v_unused_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3050_: u8 = 0;
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3055_: u8 = 0;
    let mut v_unused_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3064_: u8 = 0;
    let mut v_unused_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2967_) {
                17 => {
                    v_isSharedCheck_2975_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_2975_ == 0 {
                        v_unused_2976_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_2976_);
                        v___x_2969_ = v_x_2967_;
                        v_isShared_2970_ = v_isSharedCheck_2975_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_2969_ = leanh::lean_box(0);
                        v_isShared_2970_ = v_isSharedCheck_2975_;
                        state = 1;
                        continue;
                    }
                }
                16 => {
                    v_isSharedCheck_2985_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_2985_ == 0 {
                        v_unused_2986_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_2986_);
                        v___x_2978_ = v_x_2967_;
                        v_isShared_2979_ = v_isSharedCheck_2985_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_2978_ = leanh::lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2985_;
                        state = 3;
                        continue;
                    }
                }
                18 => {
                    v_isSharedCheck_2994_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_2994_ == 0 {
                        v_unused_2995_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_2995_);
                        v___x_2988_ = v_x_2967_;
                        v_isShared_2989_ = v_isSharedCheck_2994_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_2988_ = leanh::lean_box(0);
                        v_isShared_2989_ = v_isSharedCheck_2994_;
                        state = 5;
                        continue;
                    }
                }
                22 => {
                    v_isSharedCheck_3003_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3003_ == 0 {
                        v_unused_3004_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_3004_);
                        v___x_2997_ = v_x_2967_;
                        v_isShared_2998_ = v_isSharedCheck_3003_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_2997_ = leanh::lean_box(0);
                        v_isShared_2998_ = v_isSharedCheck_3003_;
                        state = 7;
                        continue;
                    }
                }
                19 => {
                    v_isSharedCheck_3012_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3012_ == 0 {
                        v_unused_3013_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_3013_);
                        v___x_3006_ = v_x_2967_;
                        v_isShared_3007_ = v_isSharedCheck_3012_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_3006_ = leanh::lean_box(0);
                        v_isShared_3007_ = v_isSharedCheck_3012_;
                        state = 9;
                        continue;
                    }
                }
                13 => {
                    leanh::lean_dec_ref_known(v_x_2967_, 0);
                    v_hour_3014_ = leanh::lean_ctor_get(v_time_2966_, 0);
                    v___x_3015_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_3014_);
                    v___x_3016_ = leanh::lean_box((v___x_3015_) as usize);
                    v___x_3017_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3017_, 0, v___x_3016_);
                    return v___x_3017_;
                }
                14 => {
                    v_isSharedCheck_3026_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3026_ == 0 {
                        v_unused_3027_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_3027_);
                        v___x_3019_ = v_x_2967_;
                        v_isShared_3020_ = v_isSharedCheck_3026_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_3019_ = leanh::lean_box(0);
                        v_isShared_3020_ = v_isSharedCheck_3026_;
                        state = 11;
                        continue;
                    }
                }
                15 => {
                    v_isSharedCheck_3037_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3037_ == 0 {
                        v_unused_3038_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_3038_);
                        v___x_3029_ = v_x_2967_;
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_3029_ = leanh::lean_box(0);
                        v_isShared_3030_ = v_isSharedCheck_3037_;
                        state = 13;
                        continue;
                    }
                }
                20 => {
                    v_isSharedCheck_3046_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3046_ == 0 {
                        v_unused_3047_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_3047_);
                        v___x_3040_ = v_x_2967_;
                        v_isShared_3041_ = v_isSharedCheck_3046_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_3040_ = leanh::lean_box(0);
                        v_isShared_3041_ = v_isSharedCheck_3046_;
                        state = 15;
                        continue;
                    }
                }
                21 => {
                    v_isSharedCheck_3055_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3055_ == 0 {
                        v_unused_3056_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_3056_);
                        v___x_3049_ = v_x_2967_;
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_3049_ = leanh::lean_box(0);
                        v_isShared_3050_ = v_isSharedCheck_3055_;
                        state = 17;
                        continue;
                    }
                }
                23 => {
                    v_isSharedCheck_3064_ = (!leanh::lean_is_exclusive(v_x_2967_)) as u8;
                    if v_isSharedCheck_3064_ == 0 {
                        v_unused_3065_ = leanh::lean_ctor_get(v_x_2967_, 0);
                        leanh::lean_dec(v_unused_3065_);
                        v___x_3058_ = v_x_2967_;
                        v_isShared_3059_ = v_isSharedCheck_3064_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_2967_);
                        v___x_3058_ = leanh::lean_box(0);
                        v_isShared_3059_ = v_isSharedCheck_3064_;
                        state = 19;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_2967_);
                    v___x_3066_ = leanh::lean_box(0);
                    return v___x_3066_;
                }
            },
            1 => {
                v_hour_2971_ = leanh::lean_ctor_get(v_time_2966_, 0);
                leanh::lean_inc(v_hour_2971_);
                if v_isShared_2970_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2969_, 1);
                    leanh::lean_ctor_set(v___x_2969_, 0, v_hour_2971_);
                    v___x_2973_ = v___x_2969_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_hour_2971_);
                    v___x_2973_ = v_reuseFailAlloc_2974_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2973_;
            }
            3 => {
                v_hour_2980_ = leanh::lean_ctor_get(v_time_2966_, 0);
                v___x_2981_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_2980_);
                if v_isShared_2979_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2978_, 1);
                    leanh::lean_ctor_set(v___x_2978_, 0, v___x_2981_);
                    v___x_2983_ = v___x_2978_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2984_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2984_, 0, v___x_2981_);
                    v___x_2983_ = v_reuseFailAlloc_2984_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2983_;
            }
            5 => {
                v_minute_2990_ = leanh::lean_ctor_get(v_time_2966_, 1);
                leanh::lean_inc(v_minute_2990_);
                if v_isShared_2989_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2988_, 1);
                    leanh::lean_ctor_set(v___x_2988_, 0, v_minute_2990_);
                    v___x_2992_ = v___x_2988_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_minute_2990_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2992_;
            }
            7 => {
                v_nanosecond_2999_ = leanh::lean_ctor_get(v_time_2966_, 3);
                leanh::lean_inc(v_nanosecond_2999_);
                if v_isShared_2998_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2997_, 1);
                    leanh::lean_ctor_set(v___x_2997_, 0, v_nanosecond_2999_);
                    v___x_3001_ = v___x_2997_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3002_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_nanosecond_2999_);
                    v___x_3001_ = v_reuseFailAlloc_3002_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3001_;
            }
            9 => {
                v_second_3008_ = leanh::lean_ctor_get(v_time_2966_, 2);
                leanh::lean_inc(v_second_3008_);
                if v_isShared_3007_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3006_, 1);
                    leanh::lean_ctor_set(v___x_3006_, 0, v_second_3008_);
                    v___x_3010_ = v___x_3006_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3011_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_second_3008_);
                    v___x_3010_ = v_reuseFailAlloc_3011_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3010_;
            }
            11 => {
                v_hour_3021_ = leanh::lean_ctor_get(v_time_2966_, 0);
                v___x_3022_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_3021_);
                if v_isShared_3020_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3019_, 1);
                    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3022_);
                    v___x_3024_ = v___x_3019_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
                    v___x_3024_ = v_reuseFailAlloc_3025_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3024_;
            }
            13 => {
                v_hour_3031_ = leanh::lean_ctor_get(v_time_2966_, 0);
                v___x_3032_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
                );
                v___x_3033_ = lean_int_emod(v_hour_3031_, v___x_3032_);
                if v_isShared_3030_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3029_, 1);
                    leanh::lean_ctor_set(v___x_3029_, 0, v___x_3033_);
                    v___x_3035_ = v___x_3029_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3033_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3035_;
            }
            15 => {
                v_nanosecond_3042_ = leanh::lean_ctor_get(v_time_2966_, 3);
                leanh::lean_inc(v_nanosecond_3042_);
                if v_isShared_3041_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3040_, 1);
                    leanh::lean_ctor_set(v___x_3040_, 0, v_nanosecond_3042_);
                    v___x_3044_ = v___x_3040_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_nanosecond_3042_);
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
                    leanh::lean_ctor_set_tag(v___x_3049_, 1);
                    leanh::lean_ctor_set(v___x_3049_, 0, v___x_3051_);
                    v___x_3053_ = v___x_3049_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3054_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
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
                    leanh::lean_ctor_set_tag(v___x_3058_, 1);
                    leanh::lean_ctor_set(v___x_3058_, 0, v___x_3060_);
                    v___x_3062_ = v___x_3058_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
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
    mut v_time_3067_: *mut leanh::LeanObject,
    mut v_x_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3069_ = l_Std_Time_PlainTime_format___lam__0(v_time_3067_, v_x_3068_);
    leanh::lean_dec_ref(v_time_3067_);
    return v_res_3069_;
}
pub unsafe fn l_Std_Time_PlainTime_format(
    mut v_time_3070_: *mut leanh::LeanObject,
    mut v_format_3071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3073_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3071_, v___x_3072_);
    if leanh::lean_obj_tag(v_format_3073_) == 0 {
        let mut v_a_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_time_3070_);
        v_a_3074_ = leanh::lean_ctor_get(v_format_3073_, 0);
        leanh::lean_inc(v_a_3074_);
        leanh::lean_dec_ref_known(v_format_3073_, 1);
        v___x_3075_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3076_ = lean_string_append(v___x_3075_, v_a_3074_);
        leanh::lean_dec(v_a_3074_);
        return v___x_3076_;
    } else {
        let mut v_a_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3077_ = leanh::lean_ctor_get(v_format_3073_, 0);
        leanh::lean_inc(v_a_3077_);
        leanh::lean_dec_ref_known(v_format_3073_, 1);
        v___f_3078_ = leanh::lean_alloc_closure(
            l_Std_Time_PlainTime_format___lam__0___boxed as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_3078_, 0, v_time_3070_);
        v_res_3079_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_3077_, v___f_3078_);
        if leanh::lean_obj_tag(v_res_3079_) == 0 {
            let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3080_ = l_Std_Time_PlainDate_format___closed__1;
            return v___x_3080_;
        } else {
            let mut v_val_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_3081_ = leanh::lean_ctor_get(v_res_3079_, 0);
            leanh::lean_inc(v_val_3081_);
            leanh::lean_dec_ref_known(v_res_3079_, 1);
            return v_val_3081_;
        }
    }
}
pub unsafe fn _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3082_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_3083_ = leanh::lean_unsigned_to_nat(0);
    v___x_3084_ = lean_nat_mod(v___x_3083_, v___x_3082_);
    return v___x_3084_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3085_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__0,
    );
    v___x_3086_ = lean_nat_to_int(v___x_3085_);
    return v___x_3086_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime24Hour___lam__0(
    mut v_h_3087_: *mut leanh::LeanObject,
    mut v_m_3088_: *mut leanh::LeanObject,
    mut v_s_3089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once),
        _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1,
    );
    v___x_3091_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3091_, 0, v_h_3087_);
    leanh::lean_ctor_set(v___x_3091_, 1, v_m_3088_);
    leanh::lean_ctor_set(v___x_3091_, 2, v_s_3089_);
    leanh::lean_ctor_set(v___x_3091_, 3, v___x_3090_);
    v___x_3092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3092_, 0, v___x_3091_);
    return v___x_3092_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime24Hour(
    mut v_input_3094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3095_ = l_Std_Time_PlainTime_fromTime24Hour___closed__0;
    v___x_3096_ = l_Std_Time_Formats_time24Hour;
    v___x_3097_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3096_, v___f_3095_, v_input_3094_);
    return v___x_3097_;
}
pub unsafe fn l_Std_Time_PlainTime_toTime24Hour(
    mut v_input_3098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hour_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6__overap_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hour_3099_ = leanh::lean_ctor_get(v_input_3098_, 0);
    leanh::lean_inc(v_hour_3099_);
    v_minute_3100_ = leanh::lean_ctor_get(v_input_3098_, 1);
    leanh::lean_inc(v_minute_3100_);
    v_second_3101_ = leanh::lean_ctor_get(v_input_3098_, 2);
    leanh::lean_inc(v_second_3101_);
    leanh::lean_dec_ref(v_input_3098_);
    v___x_3102_ = l_Std_Time_Formats_time24Hour;
    v___x_6__overap_3103_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3102_);
    v___x_3104_ = leanh::lean_apply_3(
        v___x_6__overap_3103_,
        v_hour_3099_,
        v_minute_3100_,
        v_second_3101_,
    );
    return v___x_3104_;
}
pub unsafe fn l_Std_Time_PlainTime_fromLeanTime24Hour___lam__0(
    mut v_h_3105_: *mut leanh::LeanObject,
    mut v_m_3106_: *mut leanh::LeanObject,
    mut v_s_3107_: *mut leanh::LeanObject,
    mut v_n_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3109_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3109_, 0, v_h_3105_);
    leanh::lean_ctor_set(v___x_3109_, 1, v_m_3106_);
    leanh::lean_ctor_set(v___x_3109_, 2, v_s_3107_);
    leanh::lean_ctor_set(v___x_3109_, 3, v_n_3108_);
    v___x_3110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3110_, 0, v___x_3109_);
    return v___x_3110_;
}
pub unsafe fn l_Std_Time_PlainTime_fromLeanTime24Hour(
    mut v_input_3112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3113_ = l_Std_Time_PlainTime_fromLeanTime24Hour___closed__0;
    v___x_3114_ = l_Std_Time_Formats_leanTime24Hour;
    leanh::lean_inc_ref(v_input_3112_);
    v___x_3115_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3114_, v___f_3113_, v_input_3112_);
    if leanh::lean_obj_tag(v___x_3115_) == 0 {
        let mut v___f_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3115_, 1);
        v___f_3116_ = l_Std_Time_PlainTime_fromTime24Hour___closed__0;
        v___x_3117_ = l_Std_Time_Formats_leanTime24HourNoNanos;
        v___x_3118_ =
            l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3117_, v___f_3116_, v_input_3112_);
        return v___x_3118_;
    } else {
        leanh::lean_dec_ref(v_input_3112_);
        return v___x_3115_;
    }
}
pub unsafe fn l_Std_Time_PlainTime_toLeanTime24Hour(
    mut v_input_3119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hour_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7__overap_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_hour_3120_ = leanh::lean_ctor_get(v_input_3119_, 0);
    leanh::lean_inc(v_hour_3120_);
    v_minute_3121_ = leanh::lean_ctor_get(v_input_3119_, 1);
    leanh::lean_inc(v_minute_3121_);
    v_second_3122_ = leanh::lean_ctor_get(v_input_3119_, 2);
    leanh::lean_inc(v_second_3122_);
    v_nanosecond_3123_ = leanh::lean_ctor_get(v_input_3119_, 3);
    leanh::lean_inc(v_nanosecond_3123_);
    leanh::lean_dec_ref(v_input_3119_);
    v___x_3124_ = l_Std_Time_Formats_leanTime24Hour;
    v___x_7__overap_3125_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3124_);
    v___x_3126_ = leanh::lean_apply_4(
        v___x_7__overap_3125_,
        v_hour_3120_,
        v_minute_3121_,
        v_second_3122_,
        v_nanosecond_3123_,
    );
    return v___x_3126_;
}
pub unsafe fn _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3127_ = leanh::lean_unsigned_to_nat(1);
    v___x_3128_ = lean_nat_to_int(v___x_3127_);
    return v___x_3128_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime12Hour___lam__0(
    mut v_h_3129_: *mut leanh::LeanObject,
    mut v_m_3130_: *mut leanh::LeanObject,
    mut v_s_3131_: *mut leanh::LeanObject,
    mut v_a_3132_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    v___x_3133_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0,
    );
    v___x_3134_ = lean_int_dec_le(v___x_3133_, v_h_3129_);
    if v___x_3134_ == 0 {
        let mut v___x_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_s_3131_);
        leanh::lean_dec(v_m_3130_);
        v___x_3135_ = leanh::lean_box(0);
        return v___x_3135_;
    } else {
        let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3137_: u8 = 0;
        v___x_3136_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
            core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
            _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
        );
        v___x_3137_ = lean_int_dec_le(v_h_3129_, v___x_3136_);
        if v___x_3137_ == 0 {
            let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_s_3131_);
            leanh::lean_dec(v_m_3130_);
            v___x_3138_ = leanh::lean_box(0);
            return v___x_3138_;
        } else {
            let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3139_ = l_Std_Time_HourMarker_toAbsolute(v_a_3132_, v_h_3129_);
            v___x_3140_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1),
                core::ptr::addr_of_mut!(
                    l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1_once
                ),
                _init_l_Std_Time_PlainTime_fromTime24Hour___lam__0___closed__1,
            );
            v___x_3141_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
            leanh::lean_ctor_set(v___x_3141_, 0, v___x_3139_);
            leanh::lean_ctor_set(v___x_3141_, 1, v_m_3130_);
            leanh::lean_ctor_set(v___x_3141_, 2, v_s_3131_);
            leanh::lean_ctor_set(v___x_3141_, 3, v___x_3140_);
            v___x_3142_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_3142_, 0, v___x_3141_);
            return v___x_3142_;
        }
    }
}
pub unsafe fn l_Std_Time_PlainTime_fromTime12Hour___lam__0___boxed(
    mut v_h_3143_: *mut leanh::LeanObject,
    mut v_m_3144_: *mut leanh::LeanObject,
    mut v_s_3145_: *mut leanh::LeanObject,
    mut v_a_3146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_3147_: u8 = 0;
    let mut v_res_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_3147_ = (leanh::lean_unbox(v_a_3146_) as u8);
    v_res_3148_ = l_Std_Time_PlainTime_fromTime12Hour___lam__0(
        v_h_3143_,
        v_m_3144_,
        v_s_3145_,
        v_a_boxed_3147_,
    );
    leanh::lean_dec(v_h_3143_);
    return v_res_3148_;
}
pub unsafe fn l_Std_Time_PlainTime_fromTime12Hour(
    mut v_input_3150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builder_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_builder_3151_ = l_Std_Time_PlainTime_fromTime12Hour___closed__0;
    v___x_3152_ = l_Std_Time_Formats_time12Hour;
    v___x_3153_ =
        l_Std_Time_GenericFormat_parseBuilder___redArg(v___x_3152_, v_builder_3151_, v_input_3150_);
    return v___x_3153_;
}
pub unsafe fn l_Std_Time_PlainTime_toTime12Hour(
    mut v_input_3154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_hour_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: u8 = 0;
    v_hour_3155_ = leanh::lean_ctor_get(v_input_3154_, 0);
    leanh::lean_inc(v_hour_3155_);
    v_minute_3156_ = leanh::lean_ctor_get(v_input_3154_, 1);
    leanh::lean_inc(v_minute_3156_);
    v_second_3157_ = leanh::lean_ctor_get(v_input_3154_, 2);
    leanh::lean_inc(v_second_3157_);
    leanh::lean_dec_ref(v_input_3154_);
    v___x_3158_ = l_Std_Time_Formats_time12Hour;
    v___x_3159_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
    );
    v___x_3160_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0_once),
        _init_l_Std_Time_PlainTime_fromTime12Hour___lam__0___closed__0,
    );
    v___x_3161_ = lean_int_emod(v_hour_3155_, v___x_3159_);
    v___x_3162_ = lean_int_add(v___x_3161_, v___x_3160_);
    leanh::lean_dec(v___x_3161_);
    v___x_3163_ = lean_int_dec_le(v___x_3159_, v_hour_3155_);
    leanh::lean_dec(v_hour_3155_);
    if v___x_3163_ == 0 {
        let mut v___x_3164_: u8 = 0;
        let mut v___x_56__overap_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3164_ = 0;
        v___x_56__overap_3165_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3158_);
        v___x_3166_ = leanh::lean_box((v___x_3164_) as usize);
        v___x_3167_ = leanh::lean_apply_4(
            v___x_56__overap_3165_,
            v___x_3162_,
            v_minute_3156_,
            v_second_3157_,
            v___x_3166_,
        );
        return v___x_3167_;
    } else {
        let mut v___x_3168_: u8 = 0;
        let mut v___x_57__overap_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3168_ = 1;
        v___x_57__overap_3169_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3158_);
        v___x_3170_ = leanh::lean_box((v___x_3168_) as usize);
        v___x_3171_ = leanh::lean_apply_4(
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
    mut v_input_3172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_input_3172_);
    v___x_3173_ = l_Std_Time_PlainTime_fromTime12Hour(v_input_3172_);
    if leanh::lean_obj_tag(v___x_3173_) == 0 {
        let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3173_, 1);
        v___x_3174_ = l_Std_Time_PlainTime_fromTime24Hour(v_input_3172_);
        return v___x_3174_;
    } else {
        leanh::lean_dec_ref(v_input_3172_);
        return v___x_3173_;
    }
}
pub unsafe fn l_Std_Time_PlainTime_instRepr___lam__0(
    mut v_data_3180_: *mut leanh::LeanObject,
    mut v___y_3181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3182_ = l_Std_Time_PlainTime_instRepr___lam__0___closed__1;
    v___x_3183_ = l_Std_Time_PlainTime_toLeanTime24Hour(v_data_3180_);
    v___x_3184_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3184_, 0, v___x_3183_);
    v___x_3185_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3185_, 0, v___x_3182_);
    leanh::lean_ctor_set(v___x_3185_, 1, v___x_3184_);
    v___x_3186_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_3187_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3187_, 0, v___x_3185_);
    leanh::lean_ctor_set(v___x_3187_, 1, v___x_3186_);
    v___x_3188_ = l_Repr_addAppParen(v___x_3187_, v___y_3181_);
    return v___x_3188_;
}
pub unsafe fn l_Std_Time_PlainTime_instRepr___lam__0___boxed(
    mut v_data_3189_: *mut leanh::LeanObject,
    mut v___y_3190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3191_ = l_Std_Time_PlainTime_instRepr___lam__0(v_data_3189_, v___y_3190_);
    leanh::lean_dec(v___y_3190_);
    return v_res_3191_;
}
pub unsafe fn _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3194_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_3195_ = lean_nat_to_int(v___x_3194_);
    return v___x_3195_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_format___lam__0(
    mut v_timezone_3196_: *mut leanh::LeanObject,
    mut v_timestamp_3197_: *mut leanh::LeanObject,
    mut v_x_3198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_offset_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_offset_3199_ = leanh::lean_ctor_get(v_timezone_3196_, 0);
    v_second_3200_ = leanh::lean_ctor_get(v_timestamp_3197_, 0);
    v_nano_3201_ = leanh::lean_ctor_get(v_timestamp_3197_, 1);
    v___x_3202_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
        _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
    );
    v___x_3203_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once),
        _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0,
    );
    v___x_3204_ = lean_int_mul(v_second_3200_, v___x_3203_);
    v___x_3205_ = lean_int_add(v___x_3204_, v_nano_3201_);
    leanh::lean_dec(v___x_3204_);
    v___x_3206_ = lean_int_mul(v_offset_3199_, v___x_3203_);
    v___x_3207_ = lean_int_add(v___x_3206_, v___x_3202_);
    leanh::lean_dec(v___x_3206_);
    v___x_3208_ = lean_int_add(v___x_3205_, v___x_3207_);
    leanh::lean_dec(v___x_3207_);
    leanh::lean_dec(v___x_3205_);
    v___x_3209_ = l_Std_Time_Duration_ofNanoseconds(v___x_3208_);
    leanh::lean_dec(v___x_3208_);
    v___x_3210_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_3209_);
    return v___x_3210_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_format___lam__0___boxed(
    mut v_timezone_3211_: *mut leanh::LeanObject,
    mut v_timestamp_3212_: *mut leanh::LeanObject,
    mut v_x_3213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3214_ =
        l_Std_Time_ZonedDateTime_format___lam__0(v_timezone_3211_, v_timestamp_3212_, v_x_3213_);
    leanh::lean_dec_ref(v_timestamp_3212_);
    leanh::lean_dec_ref(v_timezone_3211_);
    return v_res_3214_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_format(
    mut v_data_3215_: *mut leanh::LeanObject,
    mut v_format_3216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3217_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3218_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3216_, v___x_3217_);
    if leanh::lean_obj_tag(v_format_3218_) == 0 {
        let mut v_a_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3220_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_data_3215_);
        v_a_3219_ = leanh::lean_ctor_get(v_format_3218_, 0);
        leanh::lean_inc(v_a_3219_);
        leanh::lean_dec_ref_known(v_format_3218_, 1);
        v___x_3220_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3221_ = lean_string_append(v___x_3220_, v_a_3219_);
        leanh::lean_dec(v_a_3219_);
        return v___x_3221_;
    } else {
        let mut v_a_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_timestamp_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_timezone_3224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3222_ = leanh::lean_ctor_get(v_format_3218_, 0);
        leanh::lean_inc(v_a_3222_);
        leanh::lean_dec_ref_known(v_format_3218_, 1);
        v_timestamp_3223_ = leanh::lean_ctor_get(v_data_3215_, 1);
        leanh::lean_inc_ref_n(v_timestamp_3223_, 2);
        v_timezone_3224_ = leanh::lean_ctor_get(v_data_3215_, 3);
        leanh::lean_inc_ref_n(v_timezone_3224_, 2);
        leanh::lean_dec_ref(v_data_3215_);
        v___x_3225_ = leanh::lean_box(1);
        v___f_3226_ = leanh::lean_alloc_closure(
            l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_3226_, 0, v_timezone_3224_);
        leanh::lean_closure_set(v___f_3226_, 1, v_timestamp_3223_);
        v___x_3227_ = lean_mk_thunk(v___f_3226_);
        v___x_3228_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3228_, 0, v_timestamp_3223_);
        leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
        v___x_3229_ =
            l_Std_Time_GenericFormat_format(v___x_3225_, v_timezone_3224_, v_a_3222_, v___x_3228_);
        leanh::lean_dec_ref(v_timezone_3224_);
        return v___x_3229_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromISO8601String(
    mut v_input_3230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3231_ = leanh::lean_box(1);
    v___x_3232_ = l_Std_Time_Formats_iso8601;
    v___x_3233_ = l_Std_Time_GenericFormat_parse(v___x_3231_, v___x_3232_, v_input_3230_);
    return v___x_3233_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toISO8601String(
    mut v_date_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3235_ = leanh::lean_ctor_get(v_date_3234_, 1);
    leanh::lean_inc_ref_n(v_timestamp_3235_, 2);
    v_timezone_3236_ = leanh::lean_ctor_get(v_date_3234_, 3);
    leanh::lean_inc_ref_n(v_timezone_3236_, 2);
    leanh::lean_dec_ref(v_date_3234_);
    v___x_3237_ = leanh::lean_box(1);
    v___f_3238_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3238_, 0, v_timezone_3236_);
    leanh::lean_closure_set(v___f_3238_, 1, v_timestamp_3235_);
    v___x_3239_ = l_Std_Time_Formats_iso8601;
    v___x_3240_ = lean_mk_thunk(v___f_3238_);
    v___x_3241_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3241_, 0, v_timestamp_3235_);
    leanh::lean_ctor_set(v___x_3241_, 1, v___x_3240_);
    v___x_3242_ =
        l_Std_Time_GenericFormat_format(v___x_3237_, v_timezone_3236_, v___x_3239_, v___x_3241_);
    leanh::lean_dec_ref(v_timezone_3236_);
    return v___x_3242_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromRFC822String(
    mut v_input_3243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3244_ = leanh::lean_box(1);
    v___x_3245_ = l_Std_Time_Formats_rfc822;
    v___x_3246_ = l_Std_Time_GenericFormat_parse(v___x_3244_, v___x_3245_, v_input_3243_);
    return v___x_3246_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toRFC822String(
    mut v_date_3247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3248_ = leanh::lean_ctor_get(v_date_3247_, 1);
    leanh::lean_inc_ref_n(v_timestamp_3248_, 2);
    v_timezone_3249_ = leanh::lean_ctor_get(v_date_3247_, 3);
    leanh::lean_inc_ref_n(v_timezone_3249_, 2);
    leanh::lean_dec_ref(v_date_3247_);
    v___x_3250_ = leanh::lean_box(1);
    v___f_3251_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3251_, 0, v_timezone_3249_);
    leanh::lean_closure_set(v___f_3251_, 1, v_timestamp_3248_);
    v___x_3252_ = l_Std_Time_Formats_rfc822;
    v___x_3253_ = lean_mk_thunk(v___f_3251_);
    v___x_3254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3254_, 0, v_timestamp_3248_);
    leanh::lean_ctor_set(v___x_3254_, 1, v___x_3253_);
    v___x_3255_ =
        l_Std_Time_GenericFormat_format(v___x_3250_, v_timezone_3249_, v___x_3252_, v___x_3254_);
    leanh::lean_dec_ref(v_timezone_3249_);
    return v___x_3255_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromRFC850String(
    mut v_input_3256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3257_ = leanh::lean_box(1);
    v___x_3258_ = l_Std_Time_Formats_rfc850;
    v___x_3259_ = l_Std_Time_GenericFormat_parse(v___x_3257_, v___x_3258_, v_input_3256_);
    return v___x_3259_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toRFC850String(
    mut v_date_3260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3261_ = leanh::lean_ctor_get(v_date_3260_, 1);
    leanh::lean_inc_ref_n(v_timestamp_3261_, 2);
    v_timezone_3262_ = leanh::lean_ctor_get(v_date_3260_, 3);
    leanh::lean_inc_ref_n(v_timezone_3262_, 2);
    leanh::lean_dec_ref(v_date_3260_);
    v___x_3263_ = leanh::lean_box(1);
    v___f_3264_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3264_, 0, v_timezone_3262_);
    leanh::lean_closure_set(v___f_3264_, 1, v_timestamp_3261_);
    v___x_3265_ = l_Std_Time_Formats_rfc850;
    v___x_3266_ = lean_mk_thunk(v___f_3264_);
    v___x_3267_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3267_, 0, v_timestamp_3261_);
    leanh::lean_ctor_set(v___x_3267_, 1, v___x_3266_);
    v___x_3268_ =
        l_Std_Time_GenericFormat_format(v___x_3263_, v_timezone_3262_, v___x_3265_, v___x_3267_);
    leanh::lean_dec_ref(v_timezone_3262_);
    return v___x_3268_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(
    mut v_input_3269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3270_ = leanh::lean_box(1);
    v___x_3271_ = l_Std_Time_Formats_dateTimeWithZone;
    v___x_3272_ = l_Std_Time_GenericFormat_parse(v___x_3270_, v___x_3271_, v_input_3269_);
    return v___x_3272_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_toDateTimeWithZoneString(
    mut v_pdt_3273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_timestamp_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_3274_ = leanh::lean_ctor_get(v_pdt_3273_, 1);
    leanh::lean_inc_ref_n(v_timestamp_3274_, 2);
    v_timezone_3275_ = leanh::lean_ctor_get(v_pdt_3273_, 3);
    leanh::lean_inc_ref_n(v_timezone_3275_, 2);
    leanh::lean_dec_ref(v_pdt_3273_);
    v___x_3276_ = leanh::lean_box(1);
    v___f_3277_ = leanh::lean_alloc_closure(
        l_Std_Time_ZonedDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_3277_, 0, v_timezone_3275_);
    leanh::lean_closure_set(v___f_3277_, 1, v_timestamp_3274_);
    v___x_3278_ = l_Std_Time_Formats_dateTimeWithZone;
    v___x_3279_ = lean_mk_thunk(v___f_3277_);
    v___x_3280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3280_, 0, v_timestamp_3274_);
    leanh::lean_ctor_set(v___x_3280_, 1, v___x_3279_);
    v___x_3281_ =
        l_Std_Time_GenericFormat_format(v___x_3276_, v_timezone_3275_, v___x_3278_, v___x_3280_);
    leanh::lean_dec_ref(v_timezone_3275_);
    return v___x_3281_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromLeanDateTimeWithZoneString(
    mut v_input_3282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3283_ = leanh::lean_box(1);
    v___x_3284_ = l_Std_Time_Formats_leanDateTimeWithZone;
    leanh::lean_inc_ref(v_input_3282_);
    v___x_3285_ = l_Std_Time_GenericFormat_parse(v___x_3283_, v___x_3284_, v_input_3282_);
    if leanh::lean_obj_tag(v___x_3285_) == 0 {
        let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3285_, 1);
        v___x_3286_ = l_Std_Time_Formats_leanDateTimeWithZoneNoNanos;
        v___x_3287_ = l_Std_Time_GenericFormat_parse(v___x_3283_, v___x_3286_, v_input_3282_);
        return v___x_3287_;
    } else {
        leanh::lean_dec_ref(v_input_3282_);
        return v___x_3285_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(
    mut v_input_3288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3289_ = leanh::lean_box(1);
    v___x_3290_ = l_Std_Time_Formats_leanDateTimeWithIdentifier;
    leanh::lean_inc_ref(v_input_3288_);
    v___x_3291_ = l_Std_Time_GenericFormat_parse(v___x_3289_, v___x_3290_, v_input_3288_);
    if leanh::lean_obj_tag(v___x_3291_) == 0 {
        let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3291_, 1);
        v___x_3292_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
        v___x_3293_ = l_Std_Time_GenericFormat_parse(v___x_3289_, v___x_3292_, v_input_3288_);
        return v___x_3293_;
    } else {
        leanh::lean_dec_ref(v_input_3288_);
        return v___x_3291_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(
    mut v_zdt_3294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_14__overap_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_3295_ = leanh::lean_ctor_get(v_zdt_3294_, 0);
    leanh::lean_inc_ref(v_date_3295_);
    v_timezone_3296_ = leanh::lean_ctor_get(v_zdt_3294_, 3);
    leanh::lean_inc_ref(v_timezone_3296_);
    leanh::lean_dec_ref(v_zdt_3294_);
    v___x_3297_ = lean_thunk_get_own(v_date_3295_);
    leanh::lean_dec_ref(v_date_3295_);
    v_date_3298_ = leanh::lean_ctor_get(v___x_3297_, 0);
    leanh::lean_inc_ref(v_date_3298_);
    v_time_3299_ = leanh::lean_ctor_get(v___x_3297_, 1);
    leanh::lean_inc_ref(v_time_3299_);
    leanh::lean_dec(v___x_3297_);
    v_year_3300_ = leanh::lean_ctor_get(v_date_3298_, 0);
    leanh::lean_inc(v_year_3300_);
    v_month_3301_ = leanh::lean_ctor_get(v_date_3298_, 1);
    leanh::lean_inc(v_month_3301_);
    v_day_3302_ = leanh::lean_ctor_get(v_date_3298_, 2);
    leanh::lean_inc(v_day_3302_);
    leanh::lean_dec_ref(v_date_3298_);
    v_hour_3303_ = leanh::lean_ctor_get(v_time_3299_, 0);
    leanh::lean_inc(v_hour_3303_);
    v_minute_3304_ = leanh::lean_ctor_get(v_time_3299_, 1);
    leanh::lean_inc(v_minute_3304_);
    v_second_3305_ = leanh::lean_ctor_get(v_time_3299_, 2);
    leanh::lean_inc(v_second_3305_);
    v_nanosecond_3306_ = leanh::lean_ctor_get(v_time_3299_, 3);
    leanh::lean_inc(v_nanosecond_3306_);
    leanh::lean_dec_ref(v_time_3299_);
    v_offset_3307_ = leanh::lean_ctor_get(v_timezone_3296_, 0);
    leanh::lean_inc(v_offset_3307_);
    leanh::lean_dec_ref(v_timezone_3296_);
    v___x_3308_ = l_Std_Time_Formats_leanDateTimeWithZone;
    v___x_14__overap_3309_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3308_);
    v___x_3310_ = leanh::lean_apply_8(
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
    mut v_zdt_3311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_timezone_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_15__overap_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_3312_ = leanh::lean_ctor_get(v_zdt_3311_, 0);
    leanh::lean_inc_ref(v_date_3312_);
    v_timezone_3313_ = leanh::lean_ctor_get(v_zdt_3311_, 3);
    leanh::lean_inc_ref(v_timezone_3313_);
    leanh::lean_dec_ref(v_zdt_3311_);
    v___x_3314_ = lean_thunk_get_own(v_date_3312_);
    leanh::lean_dec_ref(v_date_3312_);
    v_date_3315_ = leanh::lean_ctor_get(v___x_3314_, 0);
    leanh::lean_inc_ref(v_date_3315_);
    v_time_3316_ = leanh::lean_ctor_get(v___x_3314_, 1);
    leanh::lean_inc_ref(v_time_3316_);
    leanh::lean_dec(v___x_3314_);
    v_year_3317_ = leanh::lean_ctor_get(v_date_3315_, 0);
    leanh::lean_inc(v_year_3317_);
    v_month_3318_ = leanh::lean_ctor_get(v_date_3315_, 1);
    leanh::lean_inc(v_month_3318_);
    v_day_3319_ = leanh::lean_ctor_get(v_date_3315_, 2);
    leanh::lean_inc(v_day_3319_);
    leanh::lean_dec_ref(v_date_3315_);
    v_hour_3320_ = leanh::lean_ctor_get(v_time_3316_, 0);
    leanh::lean_inc(v_hour_3320_);
    v_minute_3321_ = leanh::lean_ctor_get(v_time_3316_, 1);
    leanh::lean_inc(v_minute_3321_);
    v_second_3322_ = leanh::lean_ctor_get(v_time_3316_, 2);
    leanh::lean_inc(v_second_3322_);
    v_nanosecond_3323_ = leanh::lean_ctor_get(v_time_3316_, 3);
    leanh::lean_inc(v_nanosecond_3323_);
    leanh::lean_dec_ref(v_time_3316_);
    v_name_3324_ = leanh::lean_ctor_get(v_timezone_3313_, 1);
    leanh::lean_inc_ref(v_name_3324_);
    leanh::lean_dec_ref(v_timezone_3313_);
    v___x_3325_ = l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos;
    v___x_15__overap_3326_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3325_);
    v___x_3327_ = leanh::lean_apply_8(
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
    mut v_input_3328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_input_3328_);
    v___x_3329_ = l_Std_Time_ZonedDateTime_fromISO8601String(v_input_3328_);
    if leanh::lean_obj_tag(v___x_3329_) == 0 {
        let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3329_, 1);
        leanh::lean_inc_ref(v_input_3328_);
        v___x_3330_ = l_Std_Time_ZonedDateTime_fromRFC822String(v_input_3328_);
        if leanh::lean_obj_tag(v___x_3330_) == 0 {
            let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3330_, 1);
            leanh::lean_inc_ref(v_input_3328_);
            v___x_3331_ = l_Std_Time_ZonedDateTime_fromRFC850String(v_input_3328_);
            if leanh::lean_obj_tag(v___x_3331_) == 0 {
                let mut v___x_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_3331_, 1);
                leanh::lean_inc_ref(v_input_3328_);
                v___x_3332_ = l_Std_Time_ZonedDateTime_fromDateTimeWithZoneString(v_input_3328_);
                if leanh::lean_obj_tag(v___x_3332_) == 0 {
                    let mut v___x_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec_ref_known(v___x_3332_, 1);
                    v___x_3333_ = l_Std_Time_ZonedDateTime_fromLeanDateTimeWithIdentifierString(
                        v_input_3328_,
                    );
                    return v___x_3333_;
                } else {
                    leanh::lean_dec_ref(v_input_3328_);
                    return v___x_3332_;
                }
            } else {
                leanh::lean_dec_ref(v_input_3328_);
                return v___x_3331_;
            }
        } else {
            leanh::lean_dec_ref(v_input_3328_);
            return v___x_3330_;
        }
    } else {
        leanh::lean_dec_ref(v_input_3328_);
        return v___x_3329_;
    }
}
pub unsafe fn l_Std_Time_ZonedDateTime_instRepr___lam__0(
    mut v_data_3339_: *mut leanh::LeanObject,
    mut v___y_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Std_Time_ZonedDateTime_instRepr___lam__0___closed__1;
    v___x_3342_ = l_Std_Time_ZonedDateTime_toLeanDateTimeWithZoneString(v_data_3339_);
    v___x_3343_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3343_, 0, v___x_3342_);
    v___x_3344_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3344_, 0, v___x_3341_);
    leanh::lean_ctor_set(v___x_3344_, 1, v___x_3343_);
    v___x_3345_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_3346_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3346_, 0, v___x_3344_);
    leanh::lean_ctor_set(v___x_3346_, 1, v___x_3345_);
    v___x_3347_ = l_Repr_addAppParen(v___x_3346_, v___y_3340_);
    return v___x_3347_;
}
pub unsafe fn l_Std_Time_ZonedDateTime_instRepr___lam__0___boxed(
    mut v_data_3348_: *mut leanh::LeanObject,
    mut v___y_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3350_ = l_Std_Time_ZonedDateTime_instRepr___lam__0(v_data_3348_, v___y_3349_);
    leanh::lean_dec(v___y_3349_);
    return v_res_3350_;
}
pub unsafe fn l_Std_Time_PlainDateTime_format___lam__0(
    mut v_date_3353_: *mut leanh::LeanObject,
    mut v_locale_3354_: *mut leanh::LeanObject,
    mut v_x_3355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: u8 = 0;
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3363_: u8 = 0;
    let mut v_date_3364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3369_: u8 = 0;
    let mut v_unused_3370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3373_: u8 = 0;
    let mut v_date_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3379_: u8 = 0;
    let mut v_unused_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3383_: u8 = 0;
    let mut v_firstDayOfWeek_3384_: u8 = 0;
    let mut v_date_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3390_: u8 = 0;
    let mut v_unused_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3394_: u8 = 0;
    let mut v_date_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3398_: u8 = 0;
    let mut v_year_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3403_: u8 = 0;
    let mut v___y_3404_: u8 = 0;
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3416_: u8 = 0;
    let mut v___y_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: u8 = 0;
    let mut v___y_3422_: u8 = 0;
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: u8 = 0;
    let mut v_isSharedCheck_3441_: u8 = 0;
    let mut v_unused_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3443_: u8 = 0;
    let mut v_unused_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3447_: u8 = 0;
    let mut v_date_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3453_: u8 = 0;
    let mut v_unused_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3457_: u8 = 0;
    let mut v_firstDayOfWeek_3458_: u8 = 0;
    let mut v_date_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v_unused_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3468_: u8 = 0;
    let mut v_firstDayOfWeek_3469_: u8 = 0;
    let mut v_date_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3475_: u8 = 0;
    let mut v_unused_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3479_: u8 = 0;
    let mut v_date_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_unused_3486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v_date_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3495_: u8 = 0;
    let mut v_unused_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3503_: u8 = 0;
    let mut v_date_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: u8 = 0;
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3510_: u8 = 0;
    let mut v_unused_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3514_: u8 = 0;
    let mut v___x_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3519_: u8 = 0;
    let mut v_unused_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3523_: u8 = 0;
    let mut v_time_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3529_: u8 = 0;
    let mut v_unused_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v_time_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3540_: u8 = 0;
    let mut v_unused_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3544_: u8 = 0;
    let mut v_time_3545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3550_: u8 = 0;
    let mut v_unused_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3554_: u8 = 0;
    let mut v_time_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3560_: u8 = 0;
    let mut v_unused_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3564_: u8 = 0;
    let mut v_time_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut v_unused_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3579_: u8 = 0;
    let mut v_time_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut v_unused_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3590_: u8 = 0;
    let mut v_time_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_unused_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3602_: u8 = 0;
    let mut v_time_3603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v_unused_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3612_: u8 = 0;
    let mut v_time_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v_unused_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3622_: u8 = 0;
    let mut v_time_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3628_: u8 = 0;
    let mut v_unused_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3355_) {
                0 => {
                    leanh::lean_dec_ref_known(v_x_3355_, 0);
                    v_date_3356_ = leanh::lean_ctor_get(v_date_3353_, 0);
                    leanh::lean_inc_ref(v_date_3356_);
                    leanh::lean_dec_ref(v_date_3353_);
                    v_year_3357_ = leanh::lean_ctor_get(v_date_3356_, 0);
                    leanh::lean_inc(v_year_3357_);
                    leanh::lean_dec_ref(v_date_3356_);
                    v___x_3358_ = l_Std_Time_Year_Offset_era(v_year_3357_);
                    leanh::lean_dec(v_year_3357_);
                    v___x_3359_ = leanh::lean_box((v___x_3358_) as usize);
                    v___x_3360_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3360_, 0, v___x_3359_);
                    return v___x_3360_;
                }
                1 => {
                    v_isSharedCheck_3369_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3369_ == 0 {
                        v_unused_3370_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3370_);
                        v___x_3362_ = v_x_3355_;
                        v_isShared_3363_ = v_isSharedCheck_3369_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3362_ = leanh::lean_box(0);
                        v_isShared_3363_ = v_isSharedCheck_3369_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_isSharedCheck_3379_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3379_ == 0 {
                        v_unused_3380_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3380_);
                        v___x_3372_ = v_x_3355_;
                        v_isShared_3373_ = v_isSharedCheck_3379_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3372_ = leanh::lean_box(0);
                        v_isShared_3373_ = v_isSharedCheck_3379_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_isSharedCheck_3390_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3390_ == 0 {
                        v_unused_3391_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3391_);
                        v___x_3382_ = v_x_3355_;
                        v_isShared_3383_ = v_isSharedCheck_3390_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3382_ = leanh::lean_box(0);
                        v_isShared_3383_ = v_isSharedCheck_3390_;
                        state = 5;
                        continue;
                    }
                }
                4 => {
                    v_isSharedCheck_3443_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3443_ == 0 {
                        v_unused_3444_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3444_);
                        v___x_3393_ = v_x_3355_;
                        v_isShared_3394_ = v_isSharedCheck_3443_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3393_ = leanh::lean_box(0);
                        v_isShared_3394_ = v_isSharedCheck_3443_;
                        state = 7;
                        continue;
                    }
                }
                7 => {
                    v_isSharedCheck_3453_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3453_ == 0 {
                        v_unused_3454_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3454_);
                        v___x_3446_ = v_x_3355_;
                        v_isShared_3447_ = v_isSharedCheck_3453_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3446_ = leanh::lean_box(0);
                        v_isShared_3447_ = v_isSharedCheck_3453_;
                        state = 15;
                        continue;
                    }
                }
                8 => {
                    v_isSharedCheck_3464_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3464_ == 0 {
                        v_unused_3465_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3465_);
                        v___x_3456_ = v_x_3355_;
                        v_isShared_3457_ = v_isSharedCheck_3464_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3456_ = leanh::lean_box(0);
                        v_isShared_3457_ = v_isSharedCheck_3464_;
                        state = 17;
                        continue;
                    }
                }
                9 => {
                    v_isSharedCheck_3475_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3475_ == 0 {
                        v_unused_3476_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3476_);
                        v___x_3467_ = v_x_3355_;
                        v_isShared_3468_ = v_isSharedCheck_3475_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3467_ = leanh::lean_box(0);
                        v_isShared_3468_ = v_isSharedCheck_3475_;
                        state = 19;
                        continue;
                    }
                }
                5 => {
                    v_isSharedCheck_3485_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3485_ == 0 {
                        v_unused_3486_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3486_);
                        v___x_3478_ = v_x_3355_;
                        v_isShared_3479_ = v_isSharedCheck_3485_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3478_ = leanh::lean_box(0);
                        v_isShared_3479_ = v_isSharedCheck_3485_;
                        state = 21;
                        continue;
                    }
                }
                6 => {
                    v_isSharedCheck_3495_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3495_ == 0 {
                        v_unused_3496_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3496_);
                        v___x_3488_ = v_x_3355_;
                        v_isShared_3489_ = v_isSharedCheck_3495_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3488_ = leanh::lean_box(0);
                        v_isShared_3489_ = v_isSharedCheck_3495_;
                        state = 23;
                        continue;
                    }
                }
                10 => {
                    leanh::lean_dec_ref_known(v_x_3355_, 0);
                    v_date_3497_ = leanh::lean_ctor_get(v_date_3353_, 0);
                    leanh::lean_inc_ref(v_date_3497_);
                    leanh::lean_dec_ref(v_date_3353_);
                    v___x_3498_ = l_Std_Time_PlainDate_weekday(v_date_3497_);
                    v___x_3499_ = leanh::lean_box((v___x_3498_) as usize);
                    v___x_3500_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3500_, 0, v___x_3499_);
                    return v___x_3500_;
                }
                11 => {
                    v_isSharedCheck_3510_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3510_ == 0 {
                        v_unused_3511_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3511_);
                        v___x_3502_ = v_x_3355_;
                        v_isShared_3503_ = v_isSharedCheck_3510_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3502_ = leanh::lean_box(0);
                        v_isShared_3503_ = v_isSharedCheck_3510_;
                        state = 25;
                        continue;
                    }
                }
                12 => {
                    v_isSharedCheck_3519_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3519_ == 0 {
                        v_unused_3520_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3520_);
                        v___x_3513_ = v_x_3355_;
                        v_isShared_3514_ = v_isSharedCheck_3519_;
                        state = 27;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3513_ = leanh::lean_box(0);
                        v_isShared_3514_ = v_isSharedCheck_3519_;
                        state = 27;
                        continue;
                    }
                }
                17 => {
                    v_isSharedCheck_3529_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3529_ == 0 {
                        v_unused_3530_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3530_);
                        v___x_3522_ = v_x_3355_;
                        v_isShared_3523_ = v_isSharedCheck_3529_;
                        state = 29;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3522_ = leanh::lean_box(0);
                        v_isShared_3523_ = v_isSharedCheck_3529_;
                        state = 29;
                        continue;
                    }
                }
                16 => {
                    v_isSharedCheck_3540_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3540_ == 0 {
                        v_unused_3541_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3541_);
                        v___x_3532_ = v_x_3355_;
                        v_isShared_3533_ = v_isSharedCheck_3540_;
                        state = 31;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3532_ = leanh::lean_box(0);
                        v_isShared_3533_ = v_isSharedCheck_3540_;
                        state = 31;
                        continue;
                    }
                }
                18 => {
                    v_isSharedCheck_3550_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3550_ == 0 {
                        v_unused_3551_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3551_);
                        v___x_3543_ = v_x_3355_;
                        v_isShared_3544_ = v_isSharedCheck_3550_;
                        state = 33;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3543_ = leanh::lean_box(0);
                        v_isShared_3544_ = v_isSharedCheck_3550_;
                        state = 33;
                        continue;
                    }
                }
                22 => {
                    v_isSharedCheck_3560_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3560_ == 0 {
                        v_unused_3561_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3561_);
                        v___x_3553_ = v_x_3355_;
                        v_isShared_3554_ = v_isSharedCheck_3560_;
                        state = 35;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3553_ = leanh::lean_box(0);
                        v_isShared_3554_ = v_isSharedCheck_3560_;
                        state = 35;
                        continue;
                    }
                }
                19 => {
                    v_isSharedCheck_3570_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v_unused_3571_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3571_);
                        v___x_3563_ = v_x_3355_;
                        v_isShared_3564_ = v_isSharedCheck_3570_;
                        state = 37;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3563_ = leanh::lean_box(0);
                        v_isShared_3564_ = v_isSharedCheck_3570_;
                        state = 37;
                        continue;
                    }
                }
                13 => {
                    leanh::lean_dec_ref_known(v_x_3355_, 0);
                    v_time_3572_ = leanh::lean_ctor_get(v_date_3353_, 1);
                    leanh::lean_inc_ref(v_time_3572_);
                    leanh::lean_dec_ref(v_date_3353_);
                    v_hour_3573_ = leanh::lean_ctor_get(v_time_3572_, 0);
                    leanh::lean_inc(v_hour_3573_);
                    leanh::lean_dec_ref(v_time_3572_);
                    v___x_3574_ = l_Std_Time_HourMarker_ofOrdinal(v_hour_3573_);
                    leanh::lean_dec(v_hour_3573_);
                    v___x_3575_ = leanh::lean_box((v___x_3574_) as usize);
                    v___x_3576_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3576_, 0, v___x_3575_);
                    return v___x_3576_;
                }
                14 => {
                    v_isSharedCheck_3586_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3586_ == 0 {
                        v_unused_3587_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3587_);
                        v___x_3578_ = v_x_3355_;
                        v_isShared_3579_ = v_isSharedCheck_3586_;
                        state = 39;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3578_ = leanh::lean_box(0);
                        v_isShared_3579_ = v_isSharedCheck_3586_;
                        state = 39;
                        continue;
                    }
                }
                15 => {
                    v_isSharedCheck_3598_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3598_ == 0 {
                        v_unused_3599_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3599_);
                        v___x_3589_ = v_x_3355_;
                        v_isShared_3590_ = v_isSharedCheck_3598_;
                        state = 41;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3589_ = leanh::lean_box(0);
                        v_isShared_3590_ = v_isSharedCheck_3598_;
                        state = 41;
                        continue;
                    }
                }
                20 => {
                    v_isSharedCheck_3608_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3608_ == 0 {
                        v_unused_3609_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3609_);
                        v___x_3601_ = v_x_3355_;
                        v_isShared_3602_ = v_isSharedCheck_3608_;
                        state = 43;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3601_ = leanh::lean_box(0);
                        v_isShared_3602_ = v_isSharedCheck_3608_;
                        state = 43;
                        continue;
                    }
                }
                21 => {
                    v_isSharedCheck_3618_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3618_ == 0 {
                        v_unused_3619_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3619_);
                        v___x_3611_ = v_x_3355_;
                        v_isShared_3612_ = v_isSharedCheck_3618_;
                        state = 45;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3611_ = leanh::lean_box(0);
                        v_isShared_3612_ = v_isSharedCheck_3618_;
                        state = 45;
                        continue;
                    }
                }
                23 => {
                    v_isSharedCheck_3628_ = (!leanh::lean_is_exclusive(v_x_3355_)) as u8;
                    if v_isSharedCheck_3628_ == 0 {
                        v_unused_3629_ = leanh::lean_ctor_get(v_x_3355_, 0);
                        leanh::lean_dec(v_unused_3629_);
                        v___x_3621_ = v_x_3355_;
                        v_isShared_3622_ = v_isSharedCheck_3628_;
                        state = 47;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_3355_);
                        v___x_3621_ = leanh::lean_box(0);
                        v_isShared_3622_ = v_isSharedCheck_3628_;
                        state = 47;
                        continue;
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_3355_);
                    leanh::lean_dec_ref(v_date_3353_);
                    v___x_3630_ = leanh::lean_box(0);
                    return v___x_3630_;
                }
            },
            1 => {
                v_date_3364_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3364_);
                leanh::lean_dec_ref(v_date_3353_);
                v_year_3365_ = leanh::lean_ctor_get(v_date_3364_, 0);
                leanh::lean_inc(v_year_3365_);
                leanh::lean_dec_ref(v_date_3364_);
                if v_isShared_3363_ == 0 {
                    leanh::lean_ctor_set(v___x_3362_, 0, v_year_3365_);
                    v___x_3367_ = v___x_3362_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3368_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_year_3365_);
                    v___x_3367_ = v_reuseFailAlloc_3368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3367_;
            }
            3 => {
                v_date_3374_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3374_);
                leanh::lean_dec_ref(v_date_3353_);
                v_year_3375_ = leanh::lean_ctor_get(v_date_3374_, 0);
                leanh::lean_inc(v_year_3375_);
                leanh::lean_dec_ref(v_date_3374_);
                if v_isShared_3373_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3372_, 1);
                    leanh::lean_ctor_set(v___x_3372_, 0, v_year_3375_);
                    v___x_3377_ = v___x_3372_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3378_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3378_, 0, v_year_3375_);
                    v___x_3377_ = v_reuseFailAlloc_3378_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3377_;
            }
            5 => {
                v_firstDayOfWeek_3384_ = leanh::lean_ctor_get_uint8(
                    v_locale_3354_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_date_3385_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3385_);
                leanh::lean_dec_ref(v_date_3353_);
                v___x_3386_ = l_Std_Time_PlainDate_weekYear(v_date_3385_, v_firstDayOfWeek_3384_);
                if v_isShared_3383_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3382_, 1);
                    leanh::lean_ctor_set(v___x_3382_, 0, v___x_3386_);
                    v___x_3388_ = v___x_3382_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3386_);
                    v___x_3388_ = v_reuseFailAlloc_3389_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3388_;
            }
            7 => {
                v_date_3395_ = leanh::lean_ctor_get(v_date_3353_, 0);
                v_isSharedCheck_3441_ = (!leanh::lean_is_exclusive(v_date_3353_)) as u8;
                if v_isSharedCheck_3441_ == 0 {
                    v_unused_3442_ = leanh::lean_ctor_get(v_date_3353_, 1);
                    leanh::lean_dec(v_unused_3442_);
                    v___x_3397_ = v_date_3353_;
                    v_isShared_3398_ = v_isSharedCheck_3441_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_date_3395_);
                    leanh::lean_dec(v_date_3353_);
                    v___x_3397_ = leanh::lean_box(0);
                    v_isShared_3398_ = v_isSharedCheck_3441_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_year_3399_ = leanh::lean_ctor_get(v_date_3395_, 0);
                leanh::lean_inc(v_year_3399_);
                v_month_3400_ = leanh::lean_ctor_get(v_date_3395_, 1);
                leanh::lean_inc(v_month_3400_);
                v_day_3401_ = leanh::lean_ctor_get(v_date_3395_, 2);
                leanh::lean_inc(v_day_3401_);
                leanh::lean_dec_ref(v_date_3395_);
                v___x_3430_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_3431_ = lean_int_mod(v_year_3399_, v___x_3430_);
                v___x_3432_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_3437_ = lean_int_dec_eq(v___x_3431_, v___x_3432_);
                leanh::lean_dec(v___x_3431_);
                if v___x_3437_ == 0 {
                    v___y_3422_ = v___x_3437_;
                    state = 13;
                    continue;
                } else {
                    v___x_3438_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_3439_ = lean_int_mod(v_year_3399_, v___x_3438_);
                    v___x_3440_ = lean_int_dec_eq(v___x_3439_, v___x_3432_);
                    leanh::lean_dec(v___x_3439_);
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
                    leanh::lean_ctor_set(v___x_3397_, 1, v_day_3401_);
                    leanh::lean_ctor_set(v___x_3397_, 0, v_month_3400_);
                    v___x_3406_ = v___x_3397_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_month_3400_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_day_3401_);
                    v___x_3406_ = v_reuseFailAlloc_3413_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3407_ = l_Std_Time_ValidDate_dayOfYear(v___y_3404_, v___x_3406_);
                leanh::lean_dec_ref(v___x_3406_);
                v___x_3408_ = leanh::lean_box((v___y_3403_) as usize);
                v___x_3409_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3409_, 0, v___x_3408_);
                leanh::lean_ctor_set(v___x_3409_, 1, v___x_3407_);
                if v_isShared_3394_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3393_, 1);
                    leanh::lean_ctor_set(v___x_3393_, 0, v___x_3409_);
                    v___x_3411_ = v___x_3393_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___x_3409_);
                    v___x_3411_ = v_reuseFailAlloc_3412_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3411_;
            }
            12 => {
                v___x_3418_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_3419_ = lean_int_mod(v___y_3417_, v___x_3418_);
                leanh::lean_dec(v___y_3417_);
                v___x_3420_ = lean_int_dec_eq(v___x_3419_, v___y_3415_);
                leanh::lean_dec(v___x_3419_);
                v___y_3403_ = v___y_3416_;
                v___y_3404_ = v___x_3420_;
                state = 9;
                continue;
            }
            13 => {
                v___x_3423_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__0,
                );
                v___x_3424_ = lean_int_mod(v_year_3399_, v___x_3423_);
                v___x_3425_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
                );
                v___x_3426_ = lean_int_dec_eq(v___x_3424_, v___x_3425_);
                leanh::lean_dec(v___x_3424_);
                if v___x_3426_ == 0 {
                    leanh::lean_dec(v_year_3399_);
                    v___y_3403_ = v___y_3422_;
                    v___y_3404_ = v___x_3426_;
                    state = 9;
                    continue;
                } else {
                    v___x_3427_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDate_format___lam__0___closed__3_once
                        ),
                        _init_l_Std_Time_PlainDate_format___lam__0___closed__3,
                    );
                    v___x_3428_ = lean_int_mod(v_year_3399_, v___x_3427_);
                    v___x_3429_ = lean_int_dec_eq(v___x_3428_, v___x_3425_);
                    leanh::lean_dec(v___x_3428_);
                    if v___x_3429_ == 0 {
                        if v___x_3426_ == 0 {
                            v___y_3415_ = v___x_3425_;
                            v___y_3416_ = v___y_3422_;
                            v___y_3417_ = v_year_3399_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_dec(v_year_3399_);
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
                v___x_3434_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__2_once),
                    _init_l_Std_Time_PlainDate_format___lam__0___closed__2,
                );
                v___x_3435_ = lean_int_mod(v_year_3399_, v___x_3434_);
                v___x_3436_ = lean_int_dec_eq(v___x_3435_, v___x_3432_);
                leanh::lean_dec(v___x_3435_);
                v___y_3422_ = v___x_3436_;
                state = 13;
                continue;
            }
            15 => {
                v_date_3448_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3448_);
                leanh::lean_dec_ref(v_date_3353_);
                v___x_3449_ = l_Std_Time_PlainDate_quarter(v_date_3448_);
                leanh::lean_dec_ref(v_date_3448_);
                if v_isShared_3447_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3446_, 1);
                    leanh::lean_ctor_set(v___x_3446_, 0, v___x_3449_);
                    v___x_3451_ = v___x_3446_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3452_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
                    v___x_3451_ = v_reuseFailAlloc_3452_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3451_;
            }
            17 => {
                v_firstDayOfWeek_3458_ = leanh::lean_ctor_get_uint8(
                    v_locale_3354_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_date_3459_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3459_);
                leanh::lean_dec_ref(v_date_3353_);
                v___x_3460_ = l_Std_Time_PlainDate_weekOfYear(v_date_3459_, v_firstDayOfWeek_3458_);
                if v_isShared_3457_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3456_, 1);
                    leanh::lean_ctor_set(v___x_3456_, 0, v___x_3460_);
                    v___x_3462_ = v___x_3456_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
                    v___x_3462_ = v_reuseFailAlloc_3463_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3462_;
            }
            19 => {
                v_firstDayOfWeek_3469_ = leanh::lean_ctor_get_uint8(
                    v_locale_3354_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_date_3470_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3470_);
                leanh::lean_dec_ref(v_date_3353_);
                v___x_3471_ =
                    l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_3470_, v_firstDayOfWeek_3469_);
                if v_isShared_3468_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3467_, 1);
                    leanh::lean_ctor_set(v___x_3467_, 0, v___x_3471_);
                    v___x_3473_ = v___x_3467_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3474_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
                    v___x_3473_ = v_reuseFailAlloc_3474_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3473_;
            }
            21 => {
                v_date_3480_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3480_);
                leanh::lean_dec_ref(v_date_3353_);
                v_month_3481_ = leanh::lean_ctor_get(v_date_3480_, 1);
                leanh::lean_inc(v_month_3481_);
                leanh::lean_dec_ref(v_date_3480_);
                if v_isShared_3479_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3478_, 1);
                    leanh::lean_ctor_set(v___x_3478_, 0, v_month_3481_);
                    v___x_3483_ = v___x_3478_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_month_3481_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3483_;
            }
            23 => {
                v_date_3490_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3490_);
                leanh::lean_dec_ref(v_date_3353_);
                v_day_3491_ = leanh::lean_ctor_get(v_date_3490_, 2);
                leanh::lean_inc(v_day_3491_);
                leanh::lean_dec_ref(v_date_3490_);
                if v_isShared_3489_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3488_, 1);
                    leanh::lean_ctor_set(v___x_3488_, 0, v_day_3491_);
                    v___x_3493_ = v___x_3488_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_day_3491_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3493_;
            }
            25 => {
                v_date_3504_ = leanh::lean_ctor_get(v_date_3353_, 0);
                leanh::lean_inc_ref(v_date_3504_);
                leanh::lean_dec_ref(v_date_3353_);
                v___x_3505_ = l_Std_Time_PlainDate_weekday(v_date_3504_);
                v___x_3506_ = leanh::lean_box((v___x_3505_) as usize);
                if v_isShared_3503_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3502_, 1);
                    leanh::lean_ctor_set(v___x_3502_, 0, v___x_3506_);
                    v___x_3508_ = v___x_3502_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3509_, 0, v___x_3506_);
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
                leanh::lean_dec_ref(v_date_3353_);
                if v_isShared_3514_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3513_, 1);
                    leanh::lean_ctor_set(v___x_3513_, 0, v___x_3515_);
                    v___x_3517_ = v___x_3513_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3518_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3515_);
                    v___x_3517_ = v_reuseFailAlloc_3518_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3517_;
            }
            29 => {
                v_time_3524_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3524_);
                leanh::lean_dec_ref(v_date_3353_);
                v_hour_3525_ = leanh::lean_ctor_get(v_time_3524_, 0);
                leanh::lean_inc(v_hour_3525_);
                leanh::lean_dec_ref(v_time_3524_);
                if v_isShared_3523_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3522_, 1);
                    leanh::lean_ctor_set(v___x_3522_, 0, v_hour_3525_);
                    v___x_3527_ = v___x_3522_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3528_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v_hour_3525_);
                    v___x_3527_ = v_reuseFailAlloc_3528_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3527_;
            }
            31 => {
                v_time_3534_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3534_);
                leanh::lean_dec_ref(v_date_3353_);
                v_hour_3535_ = leanh::lean_ctor_get(v_time_3534_, 0);
                leanh::lean_inc(v_hour_3535_);
                leanh::lean_dec_ref(v_time_3534_);
                v___x_3536_ = l_Std_Time_Hour_Ordinal_shiftTo1BasedHour(v_hour_3535_);
                leanh::lean_dec(v_hour_3535_);
                if v_isShared_3533_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3532_, 1);
                    leanh::lean_ctor_set(v___x_3532_, 0, v___x_3536_);
                    v___x_3538_ = v___x_3532_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3539_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
                    v___x_3538_ = v_reuseFailAlloc_3539_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3538_;
            }
            33 => {
                v_time_3545_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3545_);
                leanh::lean_dec_ref(v_date_3353_);
                v_minute_3546_ = leanh::lean_ctor_get(v_time_3545_, 1);
                leanh::lean_inc(v_minute_3546_);
                leanh::lean_dec_ref(v_time_3545_);
                if v_isShared_3544_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3543_, 1);
                    leanh::lean_ctor_set(v___x_3543_, 0, v_minute_3546_);
                    v___x_3548_ = v___x_3543_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3549_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_minute_3546_);
                    v___x_3548_ = v_reuseFailAlloc_3549_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_3548_;
            }
            35 => {
                v_time_3555_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3555_);
                leanh::lean_dec_ref(v_date_3353_);
                v_nanosecond_3556_ = leanh::lean_ctor_get(v_time_3555_, 3);
                leanh::lean_inc(v_nanosecond_3556_);
                leanh::lean_dec_ref(v_time_3555_);
                if v_isShared_3554_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3553_, 1);
                    leanh::lean_ctor_set(v___x_3553_, 0, v_nanosecond_3556_);
                    v___x_3558_ = v___x_3553_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_nanosecond_3556_);
                    v___x_3558_ = v_reuseFailAlloc_3559_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3558_;
            }
            37 => {
                v_time_3565_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3565_);
                leanh::lean_dec_ref(v_date_3353_);
                v_second_3566_ = leanh::lean_ctor_get(v_time_3565_, 2);
                leanh::lean_inc(v_second_3566_);
                leanh::lean_dec_ref(v_time_3565_);
                if v_isShared_3564_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3563_, 1);
                    leanh::lean_ctor_set(v___x_3563_, 0, v_second_3566_);
                    v___x_3568_ = v___x_3563_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_second_3566_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3568_;
            }
            39 => {
                v_time_3580_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3580_);
                leanh::lean_dec_ref(v_date_3353_);
                v_hour_3581_ = leanh::lean_ctor_get(v_time_3580_, 0);
                leanh::lean_inc(v_hour_3581_);
                leanh::lean_dec_ref(v_time_3580_);
                v___x_3582_ = l_Std_Time_Hour_Ordinal_toRelative(v_hour_3581_);
                leanh::lean_dec(v_hour_3581_);
                if v_isShared_3579_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3578_, 1);
                    leanh::lean_ctor_set(v___x_3578_, 0, v___x_3582_);
                    v___x_3584_ = v___x_3578_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3582_);
                    v___x_3584_ = v_reuseFailAlloc_3585_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3584_;
            }
            41 => {
                v_time_3591_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3591_);
                leanh::lean_dec_ref(v_date_3353_);
                v_hour_3592_ = leanh::lean_ctor_get(v_time_3591_, 0);
                leanh::lean_inc(v_hour_3592_);
                leanh::lean_dec_ref(v_time_3591_);
                v___x_3593_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainTime_format___lam__0___closed__0_once),
                    _init_l_Std_Time_PlainTime_format___lam__0___closed__0,
                );
                v___x_3594_ = lean_int_emod(v_hour_3592_, v___x_3593_);
                leanh::lean_dec(v_hour_3592_);
                if v_isShared_3590_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3589_, 1);
                    leanh::lean_ctor_set(v___x_3589_, 0, v___x_3594_);
                    v___x_3596_ = v___x_3589_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
                    v___x_3596_ = v_reuseFailAlloc_3597_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3596_;
            }
            43 => {
                v_time_3603_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3603_);
                leanh::lean_dec_ref(v_date_3353_);
                v_nanosecond_3604_ = leanh::lean_ctor_get(v_time_3603_, 3);
                leanh::lean_inc(v_nanosecond_3604_);
                leanh::lean_dec_ref(v_time_3603_);
                if v_isShared_3602_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3601_, 1);
                    leanh::lean_ctor_set(v___x_3601_, 0, v_nanosecond_3604_);
                    v___x_3606_ = v___x_3601_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3607_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v_nanosecond_3604_);
                    v___x_3606_ = v_reuseFailAlloc_3607_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_3606_;
            }
            45 => {
                v_time_3613_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3613_);
                leanh::lean_dec_ref(v_date_3353_);
                v___x_3614_ = l_Std_Time_PlainTime_toMilliseconds(v_time_3613_);
                leanh::lean_dec_ref(v_time_3613_);
                if v_isShared_3612_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3611_, 1);
                    leanh::lean_ctor_set(v___x_3611_, 0, v___x_3614_);
                    v___x_3616_ = v___x_3611_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3617_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3617_, 0, v___x_3614_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3616_;
            }
            47 => {
                v_time_3623_ = leanh::lean_ctor_get(v_date_3353_, 1);
                leanh::lean_inc_ref(v_time_3623_);
                leanh::lean_dec_ref(v_date_3353_);
                v___x_3624_ = l_Std_Time_PlainTime_toNanoseconds(v_time_3623_);
                leanh::lean_dec_ref(v_time_3623_);
                if v_isShared_3622_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3621_, 1);
                    leanh::lean_ctor_set(v___x_3621_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3621_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3627_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
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
    mut v_date_3631_: *mut leanh::LeanObject,
    mut v_locale_3632_: *mut leanh::LeanObject,
    mut v_x_3633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3634_ = l_Std_Time_PlainDateTime_format___lam__0(v_date_3631_, v_locale_3632_, v_x_3633_);
    leanh::lean_dec_ref(v_locale_3632_);
    return v_res_3634_;
}
pub unsafe fn l_Std_Time_PlainDateTime_format(
    mut v_date_3635_: *mut leanh::LeanObject,
    mut v_format_3636_: *mut leanh::LeanObject,
    mut v_locale_3637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3638_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3639_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3636_, v___x_3638_);
    if leanh::lean_obj_tag(v_format_3639_) == 0 {
        let mut v_a_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_locale_3637_);
        leanh::lean_dec_ref(v_date_3635_);
        v_a_3640_ = leanh::lean_ctor_get(v_format_3639_, 0);
        leanh::lean_inc(v_a_3640_);
        leanh::lean_dec_ref_known(v_format_3639_, 1);
        v___x_3641_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3642_ = lean_string_append(v___x_3641_, v_a_3640_);
        leanh::lean_dec(v_a_3640_);
        return v___x_3642_;
    } else {
        let mut v_a_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_res_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3643_ = leanh::lean_ctor_get(v_format_3639_, 0);
        leanh::lean_inc(v_a_3643_);
        leanh::lean_dec_ref_known(v_format_3639_, 1);
        v___f_3644_ = leanh::lean_alloc_closure(
            l_Std_Time_PlainDateTime_format___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_3644_, 0, v_date_3635_);
        leanh::lean_closure_set(v___f_3644_, 1, v_locale_3637_);
        v_res_3645_ = l_Std_Time_GenericFormat_formatGeneric___redArg(v_a_3643_, v___f_3644_);
        if leanh::lean_obj_tag(v_res_3645_) == 0 {
            let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3646_ = l_Std_Time_PlainDate_format___closed__1;
            return v___x_3646_;
        } else {
            let mut v_val_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_3647_ = leanh::lean_ctor_get(v_res_3645_, 0);
            leanh::lean_inc(v_val_3647_);
            leanh::lean_dec_ref_known(v_res_3645_, 1);
            return v_val_3647_;
        }
    }
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3648_ = l_Std_Time_TimeZone_GMT;
    v___x_3649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3649_, 0, v___x_3648_);
    return v___x_3649_;
}
pub unsafe fn l_Std_Time_PlainDateTime_fromAscTimeString(
    mut v_input_3650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut v_a_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_date_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3651_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3652_ = l_Std_Time_Formats_ascTime;
                v___x_3653_ =
                    l_Std_Time_GenericFormat_parse(v___x_3651_, v___x_3652_, v_input_3650_);
                if leanh::lean_obj_tag(v___x_3653_) == 0 {
                    v_a_3654_ = leanh::lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3661_ = (!leanh::lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3661_ == 0 {
                        v___x_3656_ = v___x_3653_;
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3654_);
                        leanh::lean_dec(v___x_3653_);
                        v___x_3656_ = leanh::lean_box(0);
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3662_ = leanh::lean_ctor_get(v___x_3653_, 0);
                    v_isSharedCheck_3671_ = (!leanh::lean_is_exclusive(v___x_3653_)) as u8;
                    if v_isSharedCheck_3671_ == 0 {
                        v___x_3664_ = v___x_3653_;
                        v_isShared_3665_ = v_isSharedCheck_3671_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3662_);
                        leanh::lean_dec(v___x_3653_);
                        v___x_3664_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3659_;
            }
            3 => {
                v_date_3666_ = leanh::lean_ctor_get(v_a_3662_, 1);
                leanh::lean_inc_ref(v_date_3666_);
                leanh::lean_dec(v_a_3662_);
                v___x_3667_ = lean_thunk_get_own(v_date_3666_);
                leanh::lean_dec_ref(v_date_3666_);
                if v_isShared_3665_ == 0 {
                    leanh::lean_ctor_set(v___x_3664_, 0, v___x_3667_);
                    v___x_3669_ = v___x_3664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3670_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3667_);
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
    mut v_pdt_3672_: *mut leanh::LeanObject,
    mut v_x_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_pdt_3672_);
    return v_pdt_3672_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed(
    mut v_pdt_3674_: *mut leanh::LeanObject,
    mut v_x_3675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3676_ = l_Std_Time_PlainDateTime_toAscTimeString___lam__0(v_pdt_3674_, v_x_3675_);
    leanh::lean_dec_ref(v_pdt_3674_);
    return v_res_3676_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3677_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_format___lam__0___closed__1_once),
        _init_l_Std_Time_PlainDate_format___lam__0___closed__1,
    );
    v___x_3678_ = lean_int_neg(v___x_3677_);
    return v___x_3678_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toAscTimeString(
    mut v_pdt_3679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3687_: u8 = 0;
    let mut v___f_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3680_ = l_Std_Time_TimeZone_UTC;
                v_offset_3681_ = leanh::lean_ctor_get(v___x_3680_, 0);
                leanh::lean_inc_ref(v_pdt_3679_);
                v___x_3682_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_3679_);
                v_second_3683_ = leanh::lean_ctor_get(v___x_3682_, 0);
                v_nano_3684_ = leanh::lean_ctor_get(v___x_3682_, 1);
                v_isSharedCheck_3705_ = (!leanh::lean_is_exclusive(v___x_3682_)) as u8;
                if v_isSharedCheck_3705_ == 0 {
                    v___x_3686_ = v___x_3682_;
                    v_isShared_3687_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nano_3684_);
                    leanh::lean_inc(v_second_3683_);
                    leanh::lean_dec(v___x_3682_);
                    v___x_3686_ = leanh::lean_box(0);
                    v_isShared_3687_ = v_isSharedCheck_3705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3688_ = leanh::lean_alloc_closure(
                    l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3688_, 0, v_pdt_3679_);
                v___x_3689_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3690_ = l_Std_Time_Formats_ascTime;
                v___x_3691_ = lean_int_neg(v_offset_3681_);
                v___x_3692_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0,
                );
                v___x_3693_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0,
                );
                v___x_3694_ = lean_int_mul(v_second_3683_, v___x_3693_);
                leanh::lean_dec(v_second_3683_);
                v___x_3695_ = lean_int_add(v___x_3694_, v_nano_3684_);
                leanh::lean_dec(v_nano_3684_);
                leanh::lean_dec(v___x_3694_);
                v___x_3696_ = lean_int_mul(v___x_3691_, v___x_3693_);
                leanh::lean_dec(v___x_3691_);
                v___x_3697_ = lean_int_add(v___x_3696_, v___x_3692_);
                leanh::lean_dec(v___x_3696_);
                v___x_3698_ = lean_int_add(v___x_3695_, v___x_3697_);
                leanh::lean_dec(v___x_3697_);
                leanh::lean_dec(v___x_3695_);
                v_tm_3699_ = l_Std_Time_Duration_ofNanoseconds(v___x_3698_);
                leanh::lean_dec(v___x_3698_);
                v___x_3700_ = lean_mk_thunk(v___f_3688_);
                if v_isShared_3687_ == 0 {
                    leanh::lean_ctor_set(v___x_3686_, 1, v___x_3700_);
                    leanh::lean_ctor_set(v___x_3686_, 0, v_tm_3699_);
                    v___x_3702_ = v___x_3686_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3704_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_tm_3699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 1, v___x_3700_);
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
    mut v_input_3706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut v_a_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3721_: u8 = 0;
    let mut v_date_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3727_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3707_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3708_ = l_Std_Time_Formats_longDateFormat;
                v___x_3709_ =
                    l_Std_Time_GenericFormat_parse(v___x_3707_, v___x_3708_, v_input_3706_);
                if leanh::lean_obj_tag(v___x_3709_) == 0 {
                    v_a_3710_ = leanh::lean_ctor_get(v___x_3709_, 0);
                    v_isSharedCheck_3717_ = (!leanh::lean_is_exclusive(v___x_3709_)) as u8;
                    if v_isSharedCheck_3717_ == 0 {
                        v___x_3712_ = v___x_3709_;
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3710_);
                        leanh::lean_dec(v___x_3709_);
                        v___x_3712_ = leanh::lean_box(0);
                        v_isShared_3713_ = v_isSharedCheck_3717_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3718_ = leanh::lean_ctor_get(v___x_3709_, 0);
                    v_isSharedCheck_3727_ = (!leanh::lean_is_exclusive(v___x_3709_)) as u8;
                    if v_isSharedCheck_3727_ == 0 {
                        v___x_3720_ = v___x_3709_;
                        v_isShared_3721_ = v_isSharedCheck_3727_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3718_);
                        leanh::lean_dec(v___x_3709_);
                        v___x_3720_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
                    v___x_3715_ = v_reuseFailAlloc_3716_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3715_;
            }
            3 => {
                v_date_3722_ = leanh::lean_ctor_get(v_a_3718_, 1);
                leanh::lean_inc_ref(v_date_3722_);
                leanh::lean_dec(v_a_3718_);
                v___x_3723_ = lean_thunk_get_own(v_date_3722_);
                leanh::lean_dec_ref(v_date_3722_);
                if v_isShared_3721_ == 0 {
                    leanh::lean_ctor_set(v___x_3720_, 0, v___x_3723_);
                    v___x_3725_ = v___x_3720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3726_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3723_);
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
    mut v_pdt_3728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3736_: u8 = 0;
    let mut v___f_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3729_ = l_Std_Time_TimeZone_UTC;
                v_offset_3730_ = leanh::lean_ctor_get(v___x_3729_, 0);
                leanh::lean_inc_ref(v_pdt_3728_);
                v___x_3731_ = l_Std_Time_PlainDateTime_toWallTime(v_pdt_3728_);
                v_second_3732_ = leanh::lean_ctor_get(v___x_3731_, 0);
                v_nano_3733_ = leanh::lean_ctor_get(v___x_3731_, 1);
                v_isSharedCheck_3754_ = (!leanh::lean_is_exclusive(v___x_3731_)) as u8;
                if v_isSharedCheck_3754_ == 0 {
                    v___x_3735_ = v___x_3731_;
                    v_isShared_3736_ = v_isSharedCheck_3754_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_nano_3733_);
                    leanh::lean_inc(v_second_3732_);
                    leanh::lean_dec(v___x_3731_);
                    v___x_3735_ = leanh::lean_box(0);
                    v_isShared_3736_ = v_isSharedCheck_3754_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_3737_ = leanh::lean_alloc_closure(
                    l_Std_Time_PlainDateTime_toAscTimeString___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_3737_, 0, v_pdt_3728_);
                v___x_3738_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3739_ = l_Std_Time_Formats_longDateFormat;
                v___x_3740_ = lean_int_neg(v_offset_3730_);
                v___x_3741_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_toAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_toAscTimeString___closed__0,
                );
                v___x_3742_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_ZonedDateTime_format___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_ZonedDateTime_format___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_ZonedDateTime_format___lam__0___closed__0,
                );
                v___x_3743_ = lean_int_mul(v_second_3732_, v___x_3742_);
                leanh::lean_dec(v_second_3732_);
                v___x_3744_ = lean_int_add(v___x_3743_, v_nano_3733_);
                leanh::lean_dec(v_nano_3733_);
                leanh::lean_dec(v___x_3743_);
                v___x_3745_ = lean_int_mul(v___x_3740_, v___x_3742_);
                leanh::lean_dec(v___x_3740_);
                v___x_3746_ = lean_int_add(v___x_3745_, v___x_3741_);
                leanh::lean_dec(v___x_3745_);
                v___x_3747_ = lean_int_add(v___x_3744_, v___x_3746_);
                leanh::lean_dec(v___x_3746_);
                leanh::lean_dec(v___x_3744_);
                v_tm_3748_ = l_Std_Time_Duration_ofNanoseconds(v___x_3747_);
                leanh::lean_dec(v___x_3747_);
                v___x_3749_ = lean_mk_thunk(v___f_3737_);
                if v_isShared_3736_ == 0 {
                    leanh::lean_ctor_set(v___x_3735_, 1, v___x_3749_);
                    leanh::lean_ctor_set(v___x_3735_, 0, v_tm_3748_);
                    v___x_3751_ = v___x_3735_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_tm_3748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 1, v___x_3749_);
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
    mut v_input_3755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3762_: u8 = 0;
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_a_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3770_: u8 = 0;
    let mut v_date_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3776_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3756_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3757_ = l_Std_Time_Formats_dateTime24Hour;
                v___x_3758_ =
                    l_Std_Time_GenericFormat_parse(v___x_3756_, v___x_3757_, v_input_3755_);
                if leanh::lean_obj_tag(v___x_3758_) == 0 {
                    v_a_3759_ = leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3766_ = (!leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3766_ == 0 {
                        v___x_3761_ = v___x_3758_;
                        v_isShared_3762_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3759_);
                        leanh::lean_dec(v___x_3758_);
                        v___x_3761_ = leanh::lean_box(0);
                        v_isShared_3762_ = v_isSharedCheck_3766_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3767_ = leanh::lean_ctor_get(v___x_3758_, 0);
                    v_isSharedCheck_3776_ = (!leanh::lean_is_exclusive(v___x_3758_)) as u8;
                    if v_isSharedCheck_3776_ == 0 {
                        v___x_3769_ = v___x_3758_;
                        v_isShared_3770_ = v_isSharedCheck_3776_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3767_);
                        leanh::lean_dec(v___x_3758_);
                        v___x_3769_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
                    v___x_3764_ = v_reuseFailAlloc_3765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3764_;
            }
            3 => {
                v_date_3771_ = leanh::lean_ctor_get(v_a_3767_, 1);
                leanh::lean_inc_ref(v_date_3771_);
                leanh::lean_dec(v_a_3767_);
                v___x_3772_ = lean_thunk_get_own(v_date_3771_);
                leanh::lean_dec_ref(v_date_3771_);
                if v_isShared_3770_ == 0 {
                    leanh::lean_ctor_set(v___x_3769_, 0, v___x_3772_);
                    v___x_3774_ = v___x_3769_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3775_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
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
    mut v_pdt_3777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12__overap_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_3778_ = leanh::lean_ctor_get(v_pdt_3777_, 0);
    leanh::lean_inc_ref(v_date_3778_);
    v_time_3779_ = leanh::lean_ctor_get(v_pdt_3777_, 1);
    leanh::lean_inc_ref(v_time_3779_);
    leanh::lean_dec_ref(v_pdt_3777_);
    v_year_3780_ = leanh::lean_ctor_get(v_date_3778_, 0);
    leanh::lean_inc(v_year_3780_);
    v_month_3781_ = leanh::lean_ctor_get(v_date_3778_, 1);
    leanh::lean_inc(v_month_3781_);
    v_day_3782_ = leanh::lean_ctor_get(v_date_3778_, 2);
    leanh::lean_inc(v_day_3782_);
    leanh::lean_dec_ref(v_date_3778_);
    v_hour_3783_ = leanh::lean_ctor_get(v_time_3779_, 0);
    leanh::lean_inc(v_hour_3783_);
    v_minute_3784_ = leanh::lean_ctor_get(v_time_3779_, 1);
    leanh::lean_inc(v_minute_3784_);
    v_second_3785_ = leanh::lean_ctor_get(v_time_3779_, 2);
    leanh::lean_inc(v_second_3785_);
    v_nanosecond_3786_ = leanh::lean_ctor_get(v_time_3779_, 3);
    leanh::lean_inc(v_nanosecond_3786_);
    leanh::lean_dec_ref(v_time_3779_);
    v___x_3787_ = l_Std_Time_Formats_dateTime24Hour;
    v___x_12__overap_3788_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3787_);
    v___x_3789_ = leanh::lean_apply_7(
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
    mut v_input_3790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3796_: u8 = 0;
    let mut v___x_3798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3800_: u8 = 0;
    let mut v_a_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3804_: u8 = 0;
    let mut v_date_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3811_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
                );
                v___x_3812_ = l_Std_Time_Formats_leanDateTime24Hour;
                leanh::lean_inc_ref(v_input_3790_);
                v___x_3813_ =
                    l_Std_Time_GenericFormat_parse(v___x_3811_, v___x_3812_, v_input_3790_);
                if leanh::lean_obj_tag(v___x_3813_) == 0 {
                    leanh::lean_dec_ref_known(v___x_3813_, 1);
                    v___x_3814_ = l_Std_Time_Formats_leanDateTime24HourNoNanos;
                    v___x_3815_ =
                        l_Std_Time_GenericFormat_parse(v___x_3811_, v___x_3814_, v_input_3790_);
                    v___y_3792_ = v___x_3815_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_input_3790_);
                    v___y_3792_ = v___x_3813_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_3792_) == 0 {
                    v_a_3793_ = leanh::lean_ctor_get(v___y_3792_, 0);
                    v_isSharedCheck_3800_ = (!leanh::lean_is_exclusive(v___y_3792_)) as u8;
                    if v_isSharedCheck_3800_ == 0 {
                        v___x_3795_ = v___y_3792_;
                        v_isShared_3796_ = v_isSharedCheck_3800_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3793_);
                        leanh::lean_dec(v___y_3792_);
                        v___x_3795_ = leanh::lean_box(0);
                        v_isShared_3796_ = v_isSharedCheck_3800_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3801_ = leanh::lean_ctor_get(v___y_3792_, 0);
                    v_isSharedCheck_3810_ = (!leanh::lean_is_exclusive(v___y_3792_)) as u8;
                    if v_isSharedCheck_3810_ == 0 {
                        v___x_3803_ = v___y_3792_;
                        v_isShared_3804_ = v_isSharedCheck_3810_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3801_);
                        leanh::lean_dec(v___y_3792_);
                        v___x_3803_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_3799_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
                    v___x_3798_ = v_reuseFailAlloc_3799_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3798_;
            }
            4 => {
                v_date_3805_ = leanh::lean_ctor_get(v_a_3801_, 1);
                leanh::lean_inc_ref(v_date_3805_);
                leanh::lean_dec(v_a_3801_);
                v___x_3806_ = lean_thunk_get_own(v_date_3805_);
                leanh::lean_dec_ref(v_date_3805_);
                if v_isShared_3804_ == 0 {
                    leanh::lean_ctor_set(v___x_3803_, 0, v___x_3806_);
                    v___x_3808_ = v___x_3803_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 0, v___x_3806_);
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
    mut v_pdt_3816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_date_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12__overap_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_date_3817_ = leanh::lean_ctor_get(v_pdt_3816_, 0);
    leanh::lean_inc_ref(v_date_3817_);
    v_time_3818_ = leanh::lean_ctor_get(v_pdt_3816_, 1);
    leanh::lean_inc_ref(v_time_3818_);
    leanh::lean_dec_ref(v_pdt_3816_);
    v_year_3819_ = leanh::lean_ctor_get(v_date_3817_, 0);
    leanh::lean_inc(v_year_3819_);
    v_month_3820_ = leanh::lean_ctor_get(v_date_3817_, 1);
    leanh::lean_inc(v_month_3820_);
    v_day_3821_ = leanh::lean_ctor_get(v_date_3817_, 2);
    leanh::lean_inc(v_day_3821_);
    leanh::lean_dec_ref(v_date_3817_);
    v_hour_3822_ = leanh::lean_ctor_get(v_time_3818_, 0);
    leanh::lean_inc(v_hour_3822_);
    v_minute_3823_ = leanh::lean_ctor_get(v_time_3818_, 1);
    leanh::lean_inc(v_minute_3823_);
    v_second_3824_ = leanh::lean_ctor_get(v_time_3818_, 2);
    leanh::lean_inc(v_second_3824_);
    v_nanosecond_3825_ = leanh::lean_ctor_get(v_time_3818_, 3);
    leanh::lean_inc(v_nanosecond_3825_);
    leanh::lean_dec_ref(v_time_3818_);
    v___x_3826_ = l_Std_Time_Formats_leanDateTime24Hour;
    v___x_12__overap_3827_ = l_Std_Time_GenericFormat_formatBuilder___redArg(v___x_3826_);
    v___x_3828_ = leanh::lean_apply_7(
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
    mut v_date_3829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_date_3829_);
    v___x_3830_ = l_Std_Time_PlainDateTime_fromAscTimeString(v_date_3829_);
    if leanh::lean_obj_tag(v___x_3830_) == 0 {
        let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3830_, 1);
        leanh::lean_inc_ref(v_date_3829_);
        v___x_3831_ = l_Std_Time_PlainDateTime_fromLongDateFormatString(v_date_3829_);
        if leanh::lean_obj_tag(v___x_3831_) == 0 {
            let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3831_, 1);
            leanh::lean_inc_ref(v_date_3829_);
            v___x_3832_ = l_Std_Time_PlainDateTime_fromDateTimeString(v_date_3829_);
            if leanh::lean_obj_tag(v___x_3832_) == 0 {
                let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_3832_, 1);
                v___x_3833_ = l_Std_Time_PlainDateTime_fromLeanDateTimeString(v_date_3829_);
                return v___x_3833_;
            } else {
                leanh::lean_dec_ref(v_date_3829_);
                return v___x_3832_;
            }
        } else {
            leanh::lean_dec_ref(v_date_3829_);
            return v___x_3831_;
        }
    } else {
        leanh::lean_dec_ref(v_date_3829_);
        return v___x_3830_;
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_instRepr___lam__0(
    mut v_data_3839_: *mut leanh::LeanObject,
    mut v___y_3840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3841_ = l_Std_Time_PlainDateTime_instRepr___lam__0___closed__1;
    v___x_3842_ = l_Std_Time_PlainDateTime_toLeanDateTimeString(v_data_3839_);
    v___x_3843_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3843_, 0, v___x_3842_);
    v___x_3844_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3844_, 0, v___x_3841_);
    leanh::lean_ctor_set(v___x_3844_, 1, v___x_3843_);
    v___x_3845_ = l_Std_Time_PlainDate_instRepr___lam__0___closed__3;
    v___x_3846_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3846_, 0, v___x_3844_);
    leanh::lean_ctor_set(v___x_3846_, 1, v___x_3845_);
    v___x_3847_ = l_Repr_addAppParen(v___x_3846_, v___y_3840_);
    return v___x_3847_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instRepr___lam__0___boxed(
    mut v_data_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3850_ = l_Std_Time_PlainDateTime_instRepr___lam__0(v_data_3848_, v___y_3849_);
    leanh::lean_dec(v___y_3849_);
    return v_res_3850_;
}
pub unsafe fn l_Std_Time_DateTime_format(
    mut v_tz_3853_: *mut leanh::LeanObject,
    mut v_data_3854_: *mut leanh::LeanObject,
    mut v_format_3855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_format_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3856_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Formats_iso8601___closed__0_once),
        _init_l_Std_Time_Formats_iso8601___closed__0,
    );
    v_format_3857_ = l_Std_Time_GenericFormat_spec___redArg(v_format_3855_, v___x_3856_);
    if leanh::lean_obj_tag(v_format_3857_) == 0 {
        let mut v_a_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_data_3854_);
        v_a_3858_ = leanh::lean_ctor_get(v_format_3857_, 0);
        leanh::lean_inc(v_a_3858_);
        leanh::lean_dec_ref_known(v_format_3857_, 1);
        v___x_3859_ = l_Std_Time_PlainDate_format___closed__0;
        v___x_3860_ = lean_string_append(v___x_3859_, v_a_3858_);
        leanh::lean_dec(v_a_3858_);
        return v___x_3860_;
    } else {
        let mut v_a_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3861_ = leanh::lean_ctor_get(v_format_3857_, 0);
        leanh::lean_inc(v_a_3861_);
        leanh::lean_dec_ref_known(v_format_3857_, 1);
        v___x_3862_ = leanh::lean_box(1);
        v___x_3863_ =
            l_Std_Time_GenericFormat_format(v___x_3862_, v_tz_3853_, v_a_3861_, v_data_3854_);
        return v___x_3863_;
    }
}
pub unsafe fn l_Std_Time_DateTime_format___boxed(
    mut v_tz_3864_: *mut leanh::LeanObject,
    mut v_data_3865_: *mut leanh::LeanObject,
    mut v_format_3866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3867_ = l_Std_Time_DateTime_format(v_tz_3864_, v_data_3865_, v_format_3866_);
    leanh::lean_dec_ref(v_tz_3864_);
    return v_res_3867_;
}
pub unsafe fn l_Std_Time_DateTime_fromAscTimeString(
    mut v_input_3868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3869_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once),
        _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
    );
    v___x_3870_ = l_Std_Time_Formats_ascTime;
    v___x_3871_ = l_Std_Time_GenericFormat_parse(v___x_3869_, v___x_3870_, v_input_3868_);
    return v___x_3871_;
}
pub unsafe fn l_Std_Time_DateTime_toAscTimeString(
    mut v_datetime_3872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3873_ = l_Std_Time_TimeZone_GMT;
    v___x_3874_ = leanh::lean_obj_once(
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
    mut v_input_3877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_fromAscTimeString___closed__0_once),
        _init_l_Std_Time_PlainDateTime_fromAscTimeString___closed__0,
    );
    v___x_3879_ = l_Std_Time_Formats_longDateFormat;
    v___x_3880_ = l_Std_Time_GenericFormat_parse(v___x_3878_, v___x_3879_, v_input_3877_);
    return v___x_3880_;
}
pub unsafe fn l_Std_Time_DateTime_toLongDateFormatString(
    mut v_datetime_3881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3882_ = l_Std_Time_TimeZone_GMT;
    v___x_3883_ = leanh::lean_obj_once(
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
    mut v_tz_3886_: *mut leanh::LeanObject,
    mut v_date_3887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3888_ = leanh::lean_box(1);
    v___x_3889_ = l_Std_Time_Formats_iso8601;
    v___x_3890_ =
        l_Std_Time_GenericFormat_format(v___x_3888_, v_tz_3886_, v___x_3889_, v_date_3887_);
    return v___x_3890_;
}
pub unsafe fn l_Std_Time_DateTime_toISO8601String___boxed(
    mut v_tz_3891_: *mut leanh::LeanObject,
    mut v_date_3892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3893_ = l_Std_Time_DateTime_toISO8601String(v_tz_3891_, v_date_3892_);
    leanh::lean_dec_ref(v_tz_3891_);
    return v_res_3893_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC822String(
    mut v_tz_3894_: *mut leanh::LeanObject,
    mut v_date_3895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3896_ = leanh::lean_box(1);
    v___x_3897_ = l_Std_Time_Formats_rfc822;
    v___x_3898_ =
        l_Std_Time_GenericFormat_format(v___x_3896_, v_tz_3894_, v___x_3897_, v_date_3895_);
    return v___x_3898_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC822String___boxed(
    mut v_tz_3899_: *mut leanh::LeanObject,
    mut v_date_3900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3901_ = l_Std_Time_DateTime_toRFC822String(v_tz_3899_, v_date_3900_);
    leanh::lean_dec_ref(v_tz_3899_);
    return v_res_3901_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC850String(
    mut v_tz_3902_: *mut leanh::LeanObject,
    mut v_date_3903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3904_ = leanh::lean_box(1);
    v___x_3905_ = l_Std_Time_Formats_rfc850;
    v___x_3906_ =
        l_Std_Time_GenericFormat_format(v___x_3904_, v_tz_3902_, v___x_3905_, v_date_3903_);
    return v___x_3906_;
}
pub unsafe fn l_Std_Time_DateTime_toRFC850String___boxed(
    mut v_tz_3907_: *mut leanh::LeanObject,
    mut v_date_3908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ = l_Std_Time_DateTime_toRFC850String(v_tz_3907_, v_date_3908_);
    leanh::lean_dec_ref(v_tz_3907_);
    return v_res_3909_;
}
pub unsafe fn l_Std_Time_DateTime_toDateTimeWithZoneString(
    mut v_tz_3910_: *mut leanh::LeanObject,
    mut v_pdt_3911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3912_ = leanh::lean_box(1);
    v___x_3913_ = l_Std_Time_Formats_dateTimeWithZone;
    v___x_3914_ =
        l_Std_Time_GenericFormat_format(v___x_3912_, v_tz_3910_, v___x_3913_, v_pdt_3911_);
    return v___x_3914_;
}
pub unsafe fn l_Std_Time_DateTime_toDateTimeWithZoneString___boxed(
    mut v_tz_3915_: *mut leanh::LeanObject,
    mut v_pdt_3916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Std_Time_DateTime_toDateTimeWithZoneString(v_tz_3915_, v_pdt_3916_);
    leanh::lean_dec_ref(v_tz_3915_);
    return v_res_3917_;
}
pub unsafe fn l_Std_Time_DateTime_toLeanDateTimeWithZoneString(
    mut v_tz_3918_: *mut leanh::LeanObject,
    mut v_pdt_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3920_ = leanh::lean_box(1);
    v___x_3921_ = l_Std_Time_Formats_leanDateTimeWithZone;
    v___x_3922_ =
        l_Std_Time_GenericFormat_format(v___x_3920_, v_tz_3918_, v___x_3921_, v_pdt_3919_);
    return v___x_3922_;
}
pub unsafe fn l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed(
    mut v_tz_3923_: *mut leanh::LeanObject,
    mut v_pdt_3924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3925_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_3923_, v_pdt_3924_);
    leanh::lean_dec_ref(v_tz_3923_);
    return v_res_3925_;
}
pub unsafe fn l_Std_Time_DateTime_parse(
    mut v_date_3926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_date_3926_);
    v___x_3927_ = l_Std_Time_DateTime_fromAscTimeString(v_date_3926_);
    if leanh::lean_obj_tag(v___x_3927_) == 0 {
        let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3927_, 1);
        v___x_3928_ = l_Std_Time_DateTime_fromLongDateFormatString(v_date_3926_);
        return v___x_3928_;
    } else {
        leanh::lean_dec_ref(v_date_3926_);
        return v___x_3927_;
    }
}
pub unsafe fn l_Std_Time_DateTime_instRepr___lam__0(
    mut v_tz_3929_: *mut leanh::LeanObject,
    mut v_data_3930_: *mut leanh::LeanObject,
    mut v___y_3931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_Std_Time_DateTime_toLeanDateTimeWithZoneString(v_tz_3929_, v_data_3930_);
    v___x_3933_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3933_, 0, v___x_3932_);
    v___x_3934_ = l_Repr_addAppParen(v___x_3933_, v___y_3931_);
    return v___x_3934_;
}
pub unsafe fn l_Std_Time_DateTime_instRepr___lam__0___boxed(
    mut v_tz_3935_: *mut leanh::LeanObject,
    mut v_data_3936_: *mut leanh::LeanObject,
    mut v___y_3937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3938_ = l_Std_Time_DateTime_instRepr___lam__0(v_tz_3935_, v_data_3936_, v___y_3937_);
    leanh::lean_dec(v___y_3937_);
    leanh::lean_dec_ref(v_tz_3935_);
    return v_res_3938_;
}
pub unsafe fn l_Std_Time_DateTime_instRepr(
    mut v_tz_3939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3940_ = leanh::lean_alloc_closure(
        l_Std_Time_DateTime_instRepr___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_3940_, 0, v_tz_3939_);
    return v___f_3940_;
}
pub unsafe fn l_Std_Time_DateTime_instToString(
    mut v_tz_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3942_ = leanh::lean_alloc_closure(
        l_Std_Time_DateTime_toLeanDateTimeWithZoneString___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_3942_, 0, v_tz_3941_);
    return v___x_3942_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Format(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Notation_Spec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Std_Time_Formats_iso8601 = _init_l_Std_Time_Formats_iso8601();
    leanh::lean_mark_persistent(l_Std_Time_Formats_iso8601);
    l_Std_Time_Formats_americanDate = _init_l_Std_Time_Formats_americanDate();
    leanh::lean_mark_persistent(l_Std_Time_Formats_americanDate);
    l_Std_Time_Formats_europeanDate = _init_l_Std_Time_Formats_europeanDate();
    leanh::lean_mark_persistent(l_Std_Time_Formats_europeanDate);
    l_Std_Time_Formats_time12Hour = _init_l_Std_Time_Formats_time12Hour();
    leanh::lean_mark_persistent(l_Std_Time_Formats_time12Hour);
    l_Std_Time_Formats_time24Hour = _init_l_Std_Time_Formats_time24Hour();
    leanh::lean_mark_persistent(l_Std_Time_Formats_time24Hour);
    l_Std_Time_Formats_dateTime24Hour = _init_l_Std_Time_Formats_dateTime24Hour();
    leanh::lean_mark_persistent(l_Std_Time_Formats_dateTime24Hour);
    l_Std_Time_Formats_dateTimeWithZone = _init_l_Std_Time_Formats_dateTimeWithZone();
    leanh::lean_mark_persistent(l_Std_Time_Formats_dateTimeWithZone);
    l_Std_Time_Formats_leanTime24Hour = _init_l_Std_Time_Formats_leanTime24Hour();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanTime24Hour);
    l_Std_Time_Formats_leanTime24HourNoNanos = _init_l_Std_Time_Formats_leanTime24HourNoNanos();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanTime24HourNoNanos);
    l_Std_Time_Formats_leanDateTime24Hour = _init_l_Std_Time_Formats_leanDateTime24Hour();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTime24Hour);
    l_Std_Time_Formats_leanDateTime24HourNoNanos =
        _init_l_Std_Time_Formats_leanDateTime24HourNoNanos();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTime24HourNoNanos);
    l_Std_Time_Formats_leanDateTimeWithZone = _init_l_Std_Time_Formats_leanDateTimeWithZone();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithZone);
    l_Std_Time_Formats_leanDateTimeWithZoneNoNanos =
        _init_l_Std_Time_Formats_leanDateTimeWithZoneNoNanos();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithZoneNoNanos);
    l_Std_Time_Formats_leanDateTimeWithIdentifier =
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifier();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithIdentifier);
    l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos =
        _init_l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanDateTimeWithIdentifierAndNanos);
    l_Std_Time_Formats_leanDate = _init_l_Std_Time_Formats_leanDate();
    leanh::lean_mark_persistent(l_Std_Time_Formats_leanDate);
    l_Std_Time_Formats_sqlDate = _init_l_Std_Time_Formats_sqlDate();
    leanh::lean_mark_persistent(l_Std_Time_Formats_sqlDate);
    l_Std_Time_Formats_longDateFormat = _init_l_Std_Time_Formats_longDateFormat();
    leanh::lean_mark_persistent(l_Std_Time_Formats_longDateFormat);
    l_Std_Time_Formats_ascTime = _init_l_Std_Time_Formats_ascTime();
    leanh::lean_mark_persistent(l_Std_Time_Formats_ascTime);
    l_Std_Time_Formats_rfc822 = _init_l_Std_Time_Formats_rfc822();
    leanh::lean_mark_persistent(l_Std_Time_Formats_rfc822);
    l_Std_Time_Formats_rfc850 = _init_l_Std_Time_Formats_rfc850();
    leanh::lean_mark_persistent(l_Std_Time_Formats_rfc850);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Format(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Format(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Notation_Spec(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Format_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Format_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Format(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Format(builtin);
}