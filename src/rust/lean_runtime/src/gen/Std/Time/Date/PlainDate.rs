// Lean compiler output
// Module: Std.Time.Date.PlainDate
// Imports: Std.Time.Date.Basic Std.Time.Date.Unit.Month Std.Time.Date.Unit.Year
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{
    lean_int_div, lean_int_ediv, lean_int_emod, lean_int_mod,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_n,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__7_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__10_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__17_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__13_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__18_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__18_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__21_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__20_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__21_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDate_repr___redArg___closed__23_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__22_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate_repr___redArg___closed__23_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDate_repr___redArg___closed__25: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDate___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprPlainDate_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprPlainDate___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instReprPlainDate: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDate___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instInhabitedPlainDate___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__15: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__16: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDate___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDate___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainDate: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instOrdPlainDate___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDate___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDate___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDate___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__2_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Year_instOrdOffset___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__3_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Month_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__4_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__5_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_Day_instOrdOrdinal___aux__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDate___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__5_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__6_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__3_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__0_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__6_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__7_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__4_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__1_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__7_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__8_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareOn___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__5_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__2_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__8_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__9_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__7_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__8_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__9_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDate___closed__10_value: LeanClosureObject<4> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_compareLex___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 4,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__6_value) as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__9_value) as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instOrdPlainDate___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__10_value) as *mut LeanObject;
pub static mut l_Std_Time_instOrdPlainDate: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDate___closed__10_value) as *mut LeanObject;
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_instInhabited___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_instInhabited___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_PlainDate_instInhabited: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_ofEpochDay___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_ofEpochDay___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekOfMonth___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_weekOfMonth___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_toEpochDay___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_toEpochDay___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_toEpochDay___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_toEpochDay___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_rollOver___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_rollOver___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_weekday___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_weekday___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_weekday___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_weekday___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_weekday___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDate_instHAddOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_addDays___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instHAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_PlainDate_instHAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_PlainDate_instHSubOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_subDays___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instHSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_PlainDate_instHSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_addWeeks___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instHAddOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDate_instHAddOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDate_subWeeks___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDate_instHSubOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDate_instHSubOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDate_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    v___x_1114_ = lean_unsigned_to_nat(7);
    v___x_1115_ = lean_nat_to_int(v___x_1114_);
    return v___x_1115_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__0;
    v___x_1124_ = lean_string_length(v___x_1123_);
    return v___x_1124_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__15() -> *mut LeanObject {
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v___x_1125_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__14_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__14,
    );
    v___x_1126_ = lean_nat_to_int(v___x_1125_);
    return v___x_1126_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__19() -> *mut LeanObject {
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut LeanObject = core::ptr::null_mut();
    v___x_1134_ = lean_unsigned_to_nat(8);
    v___x_1135_ = lean_nat_to_int(v___x_1134_);
    return v___x_1135_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24() -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    v___x_1142_ = lean_unsigned_to_nat(9);
    v___x_1143_ = lean_nat_to_int(v___x_1142_);
    return v___x_1143_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25() -> *mut LeanObject {
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    v___x_1144_ = lean_unsigned_to_nat(0);
    v___x_1145_ = lean_nat_to_int(v___x_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Std_Time_instReprPlainDate_repr___redArg(
    mut v_x_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1156_: u8 = 0;
    let mut v___y_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: u8 = 0;
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: u8 = 0;
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1147_ = lean_ctor_get(v_x_1146_, 0);
                v_month_1148_ = lean_ctor_get(v_x_1146_, 1);
                v_day_1149_ = lean_ctor_get(v_x_1146_, 2);
                v___x_1150_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__5;
                v___x_1186_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__18;
                v___x_1187_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__19
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__19_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__19,
                );
                v___x_1210_ = lean_unsigned_to_nat(0);
                v___x_1211_ = lean_obj_once(
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
                    v___x_1214_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1214_, 0, v___x_1213_);
                    v___y_1189_ = v___x_1214_;
                    state = 2;
                    continue;
                } else {
                    v___x_1215_ = l_Int_repr(v_year_1147_);
                    v___x_1216_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1216_, 0, v___x_1215_);
                    v___x_1217_ = l_Repr_addAppParen(v___x_1216_, v___x_1210_);
                    v___y_1189_ = v___x_1217_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                lean_inc(v___y_1153_);
                v___x_1158_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1158_, 0, v___y_1153_);
                lean_ctor_set(v___x_1158_, 1, v___y_1157_);
                v___x_1159_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1159_, 0, v___x_1158_);
                lean_ctor_set_uint8(
                    v___x_1159_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_1156_,
                );
                v___x_1160_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1160_, 0, v___y_1154_);
                lean_ctor_set(v___x_1160_, 1, v___x_1159_);
                lean_inc_n(v___y_1152_, 2);
                v___x_1161_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1161_, 0, v___x_1160_);
                lean_ctor_set(v___x_1161_, 1, v___y_1152_);
                lean_inc_n(v___y_1155_, 2);
                v___x_1162_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1162_, 0, v___x_1161_);
                lean_ctor_set(v___x_1162_, 1, v___y_1155_);
                v___x_1163_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__7;
                v___x_1164_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1164_, 0, v___x_1162_);
                lean_ctor_set(v___x_1164_, 1, v___x_1163_);
                v___x_1165_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1165_, 0, v___x_1164_);
                lean_ctor_set(v___x_1165_, 1, v___x_1150_);
                v___x_1166_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                );
                v___x_1167_ = lean_unsigned_to_nat(0);
                v___x_1168_ = l_Std_Time_Day_instReprOrdinal___lam__0(v_day_1149_, v___x_1167_);
                v___x_1169_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1169_, 0, v___x_1166_);
                lean_ctor_set(v___x_1169_, 1, v___x_1168_);
                v___x_1170_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1170_, 0, v___x_1169_);
                lean_ctor_set_uint8(
                    v___x_1170_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_1156_,
                );
                v___x_1171_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1171_, 0, v___x_1165_);
                lean_ctor_set(v___x_1171_, 1, v___x_1170_);
                v___x_1172_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1172_, 0, v___x_1171_);
                lean_ctor_set(v___x_1172_, 1, v___y_1152_);
                v___x_1173_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1173_, 0, v___x_1172_);
                lean_ctor_set(v___x_1173_, 1, v___y_1155_);
                v___x_1174_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__10;
                v___x_1175_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1175_, 0, v___x_1173_);
                lean_ctor_set(v___x_1175_, 1, v___x_1174_);
                v___x_1176_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1176_, 0, v___x_1175_);
                lean_ctor_set(v___x_1176_, 1, v___x_1150_);
                v___x_1177_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__12;
                v___x_1178_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1178_, 0, v___x_1176_);
                lean_ctor_set(v___x_1178_, 1, v___x_1177_);
                v___x_1179_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__15_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__15,
                );
                v___x_1180_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__16;
                v___x_1181_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1181_, 0, v___x_1180_);
                lean_ctor_set(v___x_1181_, 1, v___x_1178_);
                v___x_1182_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__17;
                v___x_1183_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1183_, 0, v___x_1181_);
                lean_ctor_set(v___x_1183_, 1, v___x_1182_);
                v___x_1184_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1184_, 0, v___x_1179_);
                lean_ctor_set(v___x_1184_, 1, v___x_1183_);
                v___x_1185_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1185_, 0, v___x_1184_);
                lean_ctor_set_uint8(
                    v___x_1185_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___y_1156_,
                );
                return v___x_1185_;
            }
            2 => {
                v___x_1190_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1190_, 0, v___x_1187_);
                lean_ctor_set(v___x_1190_, 1, v___y_1189_);
                v___x_1191_ = 0;
                v___x_1192_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1192_, 0, v___x_1190_);
                lean_ctor_set_uint8(
                    v___x_1192_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1191_,
                );
                v___x_1193_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1193_, 0, v___x_1186_);
                lean_ctor_set(v___x_1193_, 1, v___x_1192_);
                v___x_1194_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__21;
                v___x_1195_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1195_, 0, v___x_1193_);
                lean_ctor_set(v___x_1195_, 1, v___x_1194_);
                v___x_1196_ = lean_box(1);
                v___x_1197_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1197_, 0, v___x_1195_);
                lean_ctor_set(v___x_1197_, 1, v___x_1196_);
                v___x_1198_ = l_Std_Time_instReprPlainDate_repr___redArg___closed__23;
                v___x_1199_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1199_, 0, v___x_1197_);
                lean_ctor_set(v___x_1199_, 1, v___x_1198_);
                v___x_1200_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1200_, 0, v___x_1199_);
                lean_ctor_set(v___x_1200_, 1, v___x_1150_);
                v___x_1201_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__24
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24,
                );
                v___x_1202_ = lean_unsigned_to_nat(0);
                v___x_1203_ = lean_obj_once(
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
                    v___x_1206_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1206_, 0, v___x_1205_);
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
                    v___x_1208_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_1208_, 0, v___x_1207_);
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
    mut v_x_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1219_: *mut LeanObject = core::ptr::null_mut();
    v_res_1219_ = l_Std_Time_instReprPlainDate_repr___redArg(v_x_1218_);
    lean_dec_ref(v_x_1218_);
    return v_res_1219_;
}
pub unsafe fn l_Std_Time_instReprPlainDate_repr(
    mut v_x_1220_: *mut LeanObject,
    mut v_prec_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1222_ = l_Std_Time_instReprPlainDate_repr___redArg(v_x_1220_);
    return v___x_1222_;
}
pub unsafe fn l_Std_Time_instReprPlainDate_repr___boxed(
    mut v_x_1223_: *mut LeanObject,
    mut v_prec_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1225_: *mut LeanObject = core::ptr::null_mut();
    v_res_1225_ = l_Std_Time_instReprPlainDate_repr(v_x_1223_, v_prec_1224_);
    lean_dec(v_prec_1224_);
    lean_dec_ref(v_x_1223_);
    return v_res_1225_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDate_decEq(
    mut v_x_1228_: *mut LeanObject,
    mut v_x_1229_: *mut LeanObject,
) -> u8 {
    let mut v_year_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    v_year_1230_ = lean_ctor_get(v_x_1228_, 0);
    v_month_1231_ = lean_ctor_get(v_x_1228_, 1);
    v_day_1232_ = lean_ctor_get(v_x_1228_, 2);
    v_year_1233_ = lean_ctor_get(v_x_1229_, 0);
    v_month_1234_ = lean_ctor_get(v_x_1229_, 1);
    v_day_1235_ = lean_ctor_get(v_x_1229_, 2);
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
    mut v_x_1239_: *mut LeanObject,
    mut v_x_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1241_: u8 = 0;
    let mut v_r_1242_: *mut LeanObject = core::ptr::null_mut();
    v_res_1241_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_1239_, v_x_1240_);
    lean_dec_ref(v_x_1240_);
    lean_dec_ref(v_x_1239_);
    v_r_1242_ = lean_box((v_res_1241_) as usize);
    return v_r_1242_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDate(
    mut v_x_1243_: *mut LeanObject,
    mut v_x_1244_: *mut LeanObject,
) -> u8 {
    let mut v___x_1245_: u8 = 0;
    v___x_1245_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_x_1243_, v_x_1244_);
    return v___x_1245_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDate___boxed(
    mut v_x_1246_: *mut LeanObject,
    mut v_x_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1248_: u8 = 0;
    let mut v_r_1249_: *mut LeanObject = core::ptr::null_mut();
    v_res_1248_ = l_Std_Time_instDecidableEqPlainDate(v_x_1246_, v_x_1247_);
    lean_dec_ref(v_x_1247_);
    lean_dec_ref(v_x_1246_);
    v_r_1249_ = lean_box((v_res_1248_) as usize);
    return v_r_1249_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__0() -> *mut LeanObject {
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    v___x_1250_ = lean_unsigned_to_nat(1);
    v___x_1251_ = lean_nat_to_int(v___x_1250_);
    return v___x_1251_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__1() -> *mut LeanObject {
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    v___x_1252_ = lean_unsigned_to_nat(11);
    v___x_1253_ = lean_nat_to_int(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__2() -> *mut LeanObject {
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v___x_1254_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__1,
    );
    v___x_1255_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1256_ = lean_int_add(v___x_1255_, v___x_1254_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__3() -> *mut LeanObject {
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    v___x_1257_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1258_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__2_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__2,
    );
    v___x_1259_ = lean_int_sub(v___x_1258_, v___x_1257_);
    return v___x_1259_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__4() -> *mut LeanObject {
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1262_: *mut LeanObject = core::ptr::null_mut();
    v___x_1260_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1261_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__3,
    );
    v_range_1262_ = lean_int_add(v___x_1261_, v___x_1260_);
    return v_range_1262_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__5() -> *mut LeanObject {
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    v___x_1263_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1264_ = lean_int_sub(v___x_1263_, v___x_1263_);
    return v___x_1264_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__6() -> *mut LeanObject {
    let mut v_range_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    v_range_1265_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__4,
    );
    v___x_1266_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__5,
    );
    v___x_1267_ = lean_int_emod(v___x_1266_, v_range_1265_);
    return v___x_1267_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__7() -> *mut LeanObject {
    let mut v_range_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    v_range_1268_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__4,
    );
    v___x_1269_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__6,
    );
    v___x_1270_ = lean_int_add(v___x_1269_, v_range_1268_);
    return v___x_1270_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__8() -> *mut LeanObject {
    let mut v_range_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v_range_1271_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__4,
    );
    v___x_1272_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__7_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__7,
    );
    v___x_1273_ = lean_int_emod(v___x_1272_, v_range_1271_);
    return v___x_1273_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__9() -> *mut LeanObject {
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    v___x_1274_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1275_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__8_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__8,
    );
    v___x_1276_ = lean_int_add(v___x_1275_, v___x_1274_);
    return v___x_1276_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__10() -> *mut LeanObject {
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1277_ = lean_unsigned_to_nat(30);
    v___x_1278_ = lean_nat_to_int(v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__11() -> *mut LeanObject {
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    v___x_1279_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__10_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__10,
    );
    v___x_1280_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1281_ = lean_int_add(v___x_1280_, v___x_1279_);
    return v___x_1281_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__12() -> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    v___x_1282_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1283_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__11,
    );
    v___x_1284_ = lean_int_sub(v___x_1283_, v___x_1282_);
    return v___x_1284_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__13() -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1287_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1286_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__12_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__12,
    );
    v_range_1287_ = lean_int_add(v___x_1286_, v___x_1285_);
    return v_range_1287_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__14() -> *mut LeanObject {
    let mut v_range_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    v_range_1288_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__13,
    );
    v___x_1289_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__5,
    );
    v___x_1290_ = lean_int_emod(v___x_1289_, v_range_1288_);
    return v___x_1290_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__15() -> *mut LeanObject {
    let mut v_range_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    v_range_1291_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__13,
    );
    v___x_1292_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__14,
    );
    v___x_1293_ = lean_int_add(v___x_1292_, v_range_1291_);
    return v___x_1293_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__16() -> *mut LeanObject {
    let mut v_range_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    v_range_1294_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__13,
    );
    v___x_1295_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__15_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__15,
    );
    v___x_1296_ = lean_int_emod(v___x_1295_, v_range_1294_);
    return v___x_1296_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__17() -> *mut LeanObject {
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v___x_1297_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1298_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__16_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__16,
    );
    v___x_1299_ = lean_int_add(v___x_1298_, v___x_1297_);
    return v___x_1299_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate___closed__18() -> *mut LeanObject {
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1300_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__17,
    );
    v___x_1301_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__9,
    );
    v___x_1302_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1303_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1303_, 0, v___x_1302_);
    lean_ctor_set(v___x_1303_, 1, v___x_1301_);
    lean_ctor_set(v___x_1303_, 2, v___x_1300_);
    return v___x_1303_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDate() -> *mut LeanObject {
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    v___x_1304_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__18,
    );
    return v___x_1304_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__0(
    mut v_x_1305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1306_: *mut LeanObject = core::ptr::null_mut();
    v_year_1306_ = lean_ctor_get(v_x_1305_, 0);
    lean_inc(v_year_1306_);
    return v_year_1306_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__0___boxed(
    mut v_x_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1308_: *mut LeanObject = core::ptr::null_mut();
    v_res_1308_ = l_Std_Time_instOrdPlainDate___lam__0(v_x_1307_);
    lean_dec_ref(v_x_1307_);
    return v_res_1308_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__1(
    mut v_x_1309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_month_1310_: *mut LeanObject = core::ptr::null_mut();
    v_month_1310_ = lean_ctor_get(v_x_1309_, 1);
    lean_inc(v_month_1310_);
    return v_month_1310_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__1___boxed(
    mut v_x_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1312_: *mut LeanObject = core::ptr::null_mut();
    v_res_1312_ = l_Std_Time_instOrdPlainDate___lam__1(v_x_1311_);
    lean_dec_ref(v_x_1311_);
    return v_res_1312_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__2(
    mut v_x_1313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_day_1314_: *mut LeanObject = core::ptr::null_mut();
    v_day_1314_ = lean_ctor_get(v_x_1313_, 2);
    lean_inc(v_day_1314_);
    return v_day_1314_;
}
pub unsafe fn l_Std_Time_instOrdPlainDate___lam__2___boxed(
    mut v_x_1315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1316_: *mut LeanObject = core::ptr::null_mut();
    v_res_1316_ = l_Std_Time_instOrdPlainDate___lam__2(v_x_1315_);
    lean_dec_ref(v_x_1315_);
    return v_res_1316_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0() -> *mut LeanObject {
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    v___x_1339_ = lean_unsigned_to_nat(4);
    v___x_1340_ = lean_nat_to_int(v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1() -> *mut LeanObject {
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    v___x_1341_ = lean_unsigned_to_nat(400);
    v___x_1342_ = lean_nat_to_int(v___x_1341_);
    return v___x_1342_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2() -> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    v___x_1343_ = lean_unsigned_to_nat(100);
    v___x_1344_ = lean_nat_to_int(v___x_1343_);
    return v___x_1344_;
}
pub unsafe fn l_Std_Time_PlainDate_ofYearMonthDayClip(
    mut v_year_1345_: *mut LeanObject,
    mut v_month_1346_: *mut LeanObject,
    mut v_day_1347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1349_: u8 = 0;
    let mut v_max_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: u8 = 0;
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1354_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1355_ = lean_int_mod(v_year_1345_, v___x_1354_);
                v___x_1356_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1361_ = lean_int_dec_eq(v___x_1355_, v___x_1356_);
                lean_dec(v___x_1355_);
                if v___x_1361_ == 0 {
                    v___y_1349_ = v___x_1361_;
                    state = 1;
                    continue;
                } else {
                    v___x_1362_ = lean_obj_once(
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
                    lean_dec(v___x_1363_);
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
                    lean_dec(v_max_1350_);
                    v___x_1352_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1352_, 0, v_year_1345_);
                    lean_ctor_set(v___x_1352_, 1, v_month_1346_);
                    lean_ctor_set(v___x_1352_, 2, v_day_1347_);
                    return v___x_1352_;
                } else {
                    lean_dec(v_day_1347_);
                    v___x_1353_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1353_, 0, v_year_1345_);
                    lean_ctor_set(v___x_1353_, 1, v_month_1346_);
                    lean_ctor_set(v___x_1353_, 2, v_max_1350_);
                    return v___x_1353_;
                }
            }
            2 => {
                v___x_1358_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1359_ = lean_int_mod(v_year_1345_, v___x_1358_);
                v___x_1360_ = lean_int_dec_eq(v___x_1359_, v___x_1356_);
                lean_dec(v___x_1359_);
                v___y_1349_ = v___x_1360_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Time_PlainDate_instInhabited___closed__0() -> *mut LeanObject {
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    v___x_1365_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__17,
    );
    v___x_1366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__9,
    );
    v___x_1367_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
    );
    v___x_1368_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1368_, 0, v___x_1367_);
    lean_ctor_set(v___x_1368_, 1, v___x_1366_);
    lean_ctor_set(v___x_1368_, 2, v___x_1365_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_instInhabited() -> *mut LeanObject {
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    v___x_1369_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_instInhabited___closed__0_once),
        _init_l_Std_Time_PlainDate_instInhabited___closed__0,
    );
    return v___x_1369_;
}
pub unsafe fn l_Std_Time_PlainDate_ofYearMonthDay_x3f(
    mut v_year_1370_: *mut LeanObject,
    mut v_month_1371_: *mut LeanObject,
    mut v_day_1372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1374_: u8 = 0;
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: u8 = 0;
    let mut v___x_1387_: u8 = 0;
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1380_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1381_ = lean_int_mod(v_year_1370_, v___x_1380_);
                v___x_1382_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1387_ = lean_int_dec_eq(v___x_1381_, v___x_1382_);
                lean_dec(v___x_1381_);
                if v___x_1387_ == 0 {
                    v___y_1374_ = v___x_1387_;
                    state = 1;
                    continue;
                } else {
                    v___x_1388_ = lean_obj_once(
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
                    lean_dec(v___x_1389_);
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
                lean_dec(v___x_1375_);
                if v___x_1376_ == 0 {
                    lean_dec(v_day_1372_);
                    lean_dec(v_month_1371_);
                    lean_dec(v_year_1370_);
                    v___x_1377_ = lean_box(0);
                    return v___x_1377_;
                } else {
                    v___x_1378_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1378_, 0, v_year_1370_);
                    lean_ctor_set(v___x_1378_, 1, v_month_1371_);
                    lean_ctor_set(v___x_1378_, 2, v_day_1372_);
                    v___x_1379_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1379_, 0, v___x_1378_);
                    return v___x_1379_;
                }
            }
            2 => {
                v___x_1384_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1385_ = lean_int_mod(v_year_1370_, v___x_1384_);
                v___x_1386_ = lean_int_dec_eq(v___x_1385_, v___x_1382_);
                lean_dec(v___x_1385_);
                v___y_1374_ = v___x_1386_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_ofYearOrdinal(
    mut v_year_1391_: *mut LeanObject,
    mut v_ordinal_1392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1394_: u8 = 0;
    let mut v_val_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1399_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1400_ = lean_int_mod(v_year_1391_, v___x_1399_);
                v___x_1401_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1406_ = lean_int_dec_eq(v___x_1400_, v___x_1401_);
                lean_dec(v___x_1400_);
                if v___x_1406_ == 0 {
                    v___y_1394_ = v___x_1406_;
                    state = 1;
                    continue;
                } else {
                    v___x_1407_ = lean_obj_once(
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
                    lean_dec(v___x_1408_);
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
                v_fst_1396_ = lean_ctor_get(v_val_1395_, 0);
                lean_inc(v_fst_1396_);
                v_snd_1397_ = lean_ctor_get(v_val_1395_, 1);
                lean_inc(v_snd_1397_);
                lean_dec_ref(v_val_1395_);
                v___x_1398_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1398_, 0, v_year_1391_);
                lean_ctor_set(v___x_1398_, 1, v_fst_1396_);
                lean_ctor_set(v___x_1398_, 2, v_snd_1397_);
                return v___x_1398_;
            }
            2 => {
                v___x_1403_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1404_ = lean_int_mod(v_year_1391_, v___x_1403_);
                v___x_1405_ = lean_int_dec_eq(v___x_1404_, v___x_1401_);
                lean_dec(v___x_1404_);
                v___y_1394_ = v___x_1405_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_ofYearOrdinal___boxed(
    mut v_year_1410_: *mut LeanObject,
    mut v_ordinal_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1412_: *mut LeanObject = core::ptr::null_mut();
    v_res_1412_ = l_Std_Time_PlainDate_ofYearOrdinal(v_year_1410_, v_ordinal_1411_);
    lean_dec(v_ordinal_1411_);
    return v_res_1412_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__0() -> *mut LeanObject {
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    v___x_1413_ = lean_unsigned_to_nat(719468);
    v___x_1414_ = lean_nat_to_int(v___x_1413_);
    return v___x_1414_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__1() -> *mut LeanObject {
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    v___x_1415_ = lean_unsigned_to_nat(31);
    v___x_1416_ = lean_nat_to_int(v___x_1415_);
    return v___x_1416_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__2() -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ = lean_unsigned_to_nat(12);
    v___x_1418_ = lean_nat_to_int(v___x_1417_);
    return v___x_1418_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__3() -> *mut LeanObject {
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1419_ = lean_unsigned_to_nat(146097);
    v___x_1420_ = lean_nat_to_int(v___x_1419_);
    return v___x_1420_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__4() -> *mut LeanObject {
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    v___x_1421_ = lean_unsigned_to_nat(1460);
    v___x_1422_ = lean_nat_to_int(v___x_1421_);
    return v___x_1422_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__5() -> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    v___x_1423_ = lean_unsigned_to_nat(36524);
    v___x_1424_ = lean_nat_to_int(v___x_1423_);
    return v___x_1424_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__6() -> *mut LeanObject {
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1425_ = lean_unsigned_to_nat(146096);
    v___x_1426_ = lean_nat_to_int(v___x_1425_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__7() -> *mut LeanObject {
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1427_ = lean_unsigned_to_nat(365);
    v___x_1428_ = lean_nat_to_int(v___x_1427_);
    return v___x_1428_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__8() -> *mut LeanObject {
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1429_ = lean_unsigned_to_nat(5);
    v___x_1430_ = lean_nat_to_int(v___x_1429_);
    return v___x_1430_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__9() -> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = lean_unsigned_to_nat(2);
    v___x_1432_ = lean_nat_to_int(v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__10() -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_unsigned_to_nat(153);
    v___x_1434_ = lean_nat_to_int(v___x_1433_);
    return v___x_1434_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__11() -> *mut LeanObject {
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    v___x_1435_ = lean_unsigned_to_nat(10);
    v___x_1436_ = lean_nat_to_int(v___x_1435_);
    return v___x_1436_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__12() -> *mut LeanObject {
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__24_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__24,
    );
    v___x_1438_ = lean_int_neg(v___x_1437_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_ofEpochDay___closed__13() -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = lean_unsigned_to_nat(3);
    v___x_1440_ = lean_nat_to_int(v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Std_Time_PlainDate_ofEpochDay(mut v_day_1441_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1446_: u8 = 0;
    let mut v_max_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: u8 = 0;
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_z_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: u8 = 0;
    let mut v___y_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: u8 = 0;
    let mut v___y_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: u8 = 0;
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___y_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: u8 = 0;
    let mut v___y_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___y_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_era_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doe_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_yoe_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_y_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doy_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mp_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1451_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__0,
                );
                v_z_1452_ = lean_int_add(v_day_1441_, v___x_1451_);
                v___x_1453_ = lean_obj_once(
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
                    v___x_1553_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__6,
                    );
                    v___x_1554_ = lean_int_sub(v_z_1452_, v___x_1553_);
                    v___y_1509_ = v___x_1554_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_z_1452_);
                    v___y_1509_ = v_z_1452_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                v_max_1447_ = l_Std_Time_Month_Ordinal_days(v___y_1446_, v___y_1444_);
                v___x_1448_ = lean_int_dec_lt(v_max_1447_, v___y_1445_);
                if v___x_1448_ == 0 {
                    lean_dec(v_max_1447_);
                    v___x_1449_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1449_, 0, v___y_1443_);
                    lean_ctor_set(v___x_1449_, 1, v___y_1444_);
                    lean_ctor_set(v___x_1449_, 2, v___y_1445_);
                    return v___x_1449_;
                } else {
                    lean_dec(v___y_1445_);
                    v___x_1450_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1450_, 0, v___y_1443_);
                    lean_ctor_set(v___x_1450_, 1, v___y_1444_);
                    lean_ctor_set(v___x_1450_, 2, v_max_1447_);
                    return v___x_1450_;
                }
            }
            2 => {
                v___x_1459_ = lean_int_mod(v___y_1456_, v___y_1455_);
                v___x_1460_ = lean_int_dec_eq(v___x_1459_, v___x_1453_);
                lean_dec(v___x_1459_);
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
                lean_dec(v___x_1468_);
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
                    lean_dec(v___x_1470_);
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
                    lean_dec(v___y_1477_);
                    lean_inc(v___y_1478_);
                    v___y_1462_ = v___y_1473_;
                    v___y_1463_ = v___y_1476_;
                    v___y_1464_ = v___y_1475_;
                    v___y_1465_ = v___y_1474_;
                    v___y_1466_ = v___y_1479_;
                    v___y_1467_ = v___y_1478_;
                    state = 3;
                    continue;
                } else {
                    v___x_1481_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__1),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__1_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__1,
                    );
                    v___x_1482_ = lean_int_dec_le(v___y_1477_, v___x_1481_);
                    if v___x_1482_ == 0 {
                        lean_dec(v___y_1477_);
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
                lean_dec(v___y_1489_);
                v___x_1493_ = lean_int_dec_le(v___y_1488_, v___y_1490_);
                if v___x_1493_ == 0 {
                    lean_dec(v___y_1490_);
                    lean_inc(v___y_1488_);
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
                    v___x_1494_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
                    );
                    v___x_1495_ = lean_int_dec_le(v___y_1490_, v___x_1494_);
                    if v___x_1495_ == 0 {
                        lean_dec(v___y_1490_);
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
                lean_dec(v___y_1500_);
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
                v___x_1510_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__3,
                );
                v_era_1511_ = lean_int_div(v___y_1509_, v___x_1510_);
                lean_dec(v___y_1509_);
                v___x_1512_ = lean_int_mul(v_era_1511_, v___x_1510_);
                v_doe_1513_ = lean_int_sub(v_z_1452_, v___x_1512_);
                lean_dec(v___x_1512_);
                lean_dec(v_z_1452_);
                v___x_1514_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__4),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__4_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__4,
                );
                v___x_1515_ = lean_int_div(v_doe_1513_, v___x_1514_);
                v___x_1516_ = lean_int_sub(v_doe_1513_, v___x_1515_);
                lean_dec(v___x_1515_);
                v___x_1517_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__5_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__5,
                );
                v___x_1518_ = lean_int_div(v_doe_1513_, v___x_1517_);
                v___x_1519_ = lean_int_add(v___x_1516_, v___x_1518_);
                lean_dec(v___x_1518_);
                lean_dec(v___x_1516_);
                v___x_1520_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__6_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__6,
                );
                v___x_1521_ = lean_int_div(v_doe_1513_, v___x_1520_);
                v___x_1522_ = lean_int_sub(v___x_1519_, v___x_1521_);
                lean_dec(v___x_1521_);
                lean_dec(v___x_1519_);
                v___x_1523_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__7,
                );
                v_yoe_1524_ = lean_int_div(v___x_1522_, v___x_1523_);
                lean_dec(v___x_1522_);
                v___x_1525_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1526_ = lean_int_mul(v_era_1511_, v___x_1525_);
                lean_dec(v_era_1511_);
                v_y_1527_ = lean_int_add(v_yoe_1524_, v___x_1526_);
                lean_dec(v___x_1526_);
                v___x_1528_ = lean_int_mul(v___x_1523_, v_yoe_1524_);
                v___x_1529_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1530_ = lean_int_div(v_yoe_1524_, v___x_1529_);
                v___x_1531_ = lean_int_add(v___x_1528_, v___x_1530_);
                lean_dec(v___x_1530_);
                lean_dec(v___x_1528_);
                v___x_1532_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                );
                v___x_1533_ = lean_int_div(v_yoe_1524_, v___x_1532_);
                lean_dec(v_yoe_1524_);
                v___x_1534_ = lean_int_sub(v___x_1531_, v___x_1533_);
                lean_dec(v___x_1533_);
                lean_dec(v___x_1531_);
                v_doy_1535_ = lean_int_sub(v_doe_1513_, v___x_1534_);
                lean_dec(v___x_1534_);
                lean_dec(v_doe_1513_);
                v___x_1536_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__8,
                );
                v___x_1537_ = lean_int_mul(v___x_1536_, v_doy_1535_);
                v___x_1538_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__9,
                );
                v___x_1539_ = lean_int_add(v___x_1537_, v___x_1538_);
                lean_dec(v___x_1537_);
                v___x_1540_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__10,
                );
                v_mp_1541_ = lean_int_div(v___x_1539_, v___x_1540_);
                lean_dec(v___x_1539_);
                v___x_1542_ = lean_int_mul(v___x_1540_, v_mp_1541_);
                v___x_1543_ = lean_int_add(v___x_1542_, v___x_1538_);
                lean_dec(v___x_1542_);
                v___x_1544_ = lean_int_div(v___x_1543_, v___x_1536_);
                lean_dec(v___x_1543_);
                v___x_1545_ = lean_int_sub(v_doy_1535_, v___x_1544_);
                lean_dec(v___x_1544_);
                lean_dec(v_doy_1535_);
                v___x_1546_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v_d_1547_ = lean_int_add(v___x_1545_, v___x_1546_);
                lean_dec(v___x_1545_);
                v___x_1548_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__11,
                );
                v___x_1549_ = lean_int_dec_lt(v_mp_1541_, v___x_1548_);
                if v___x_1549_ == 0 {
                    v___x_1550_ = lean_obj_once(
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
                    v___x_1551_ = lean_obj_once(
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
    mut v_day_1555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1556_: *mut LeanObject = core::ptr::null_mut();
    v_res_1556_ = l_Std_Time_PlainDate_ofEpochDay(v_day_1555_);
    lean_dec(v_day_1555_);
    return v_res_1556_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekOfMonth___closed__0() -> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    v___x_1557_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1558_ = lean_int_neg(v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l_Std_Time_PlainDate_weekOfMonth(
    mut v_date_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_day_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    v_day_1560_ = lean_ctor_get(v_date_1559_, 2);
    v___x_1561_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1562_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v___x_1563_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0_once),
        _init_l_Std_Time_PlainDate_weekOfMonth___closed__0,
    );
    v___x_1564_ = lean_int_add(v_day_1560_, v___x_1563_);
    v___x_1565_ = lean_int_ediv(v___x_1564_, v___x_1562_);
    lean_dec(v___x_1564_);
    v___x_1566_ = lean_int_add(v___x_1565_, v___x_1561_);
    lean_dec(v___x_1565_);
    return v___x_1566_;
}
pub unsafe fn l_Std_Time_PlainDate_weekOfMonth___boxed(
    mut v_date_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1568_: *mut LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Std_Time_PlainDate_weekOfMonth(v_date_1567_);
    lean_dec_ref(v_date_1567_);
    return v_res_1568_;
}
pub unsafe fn l_Std_Time_PlainDate_quarter(mut v_date_1569_: *mut LeanObject) -> *mut LeanObject {
    let mut v_month_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v_month_1570_ = lean_ctor_get(v_date_1569_, 1);
    v___x_1571_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1572_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__13,
    );
    v___x_1573_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekOfMonth___closed__0_once),
        _init_l_Std_Time_PlainDate_weekOfMonth___closed__0,
    );
    v___x_1574_ = lean_int_add(v_month_1570_, v___x_1573_);
    v___x_1575_ = lean_int_ediv(v___x_1574_, v___x_1572_);
    lean_dec(v___x_1574_);
    v___x_1576_ = lean_int_add(v___x_1575_, v___x_1571_);
    lean_dec(v___x_1575_);
    return v___x_1576_;
}
pub unsafe fn l_Std_Time_PlainDate_quarter___boxed(
    mut v_date_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1578_: *mut LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Std_Time_PlainDate_quarter(v_date_1577_);
    lean_dec_ref(v_date_1577_);
    return v_res_1578_;
}
pub unsafe fn l_Std_Time_PlainDate_dayOfYear(mut v_date_1579_: *mut LeanObject) -> *mut LeanObject {
    let mut v_year_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1580_ = lean_ctor_get(v_date_1579_, 0);
                v_month_1581_ = lean_ctor_get(v_date_1579_, 1);
                v_day_1582_ = lean_ctor_get(v_date_1579_, 2);
                v___x_1587_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1588_ = lean_int_mod(v_year_1580_, v___x_1587_);
                v___x_1589_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1594_ = lean_int_dec_eq(v___x_1588_, v___x_1589_);
                lean_dec(v___x_1588_);
                if v___x_1594_ == 0 {
                    v___y_1584_ = v___x_1594_;
                    state = 1;
                    continue;
                } else {
                    v___x_1595_ = lean_obj_once(
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
                    lean_dec(v___x_1596_);
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
                lean_inc(v_day_1582_);
                lean_inc(v_month_1581_);
                v___x_1585_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1585_, 0, v_month_1581_);
                lean_ctor_set(v___x_1585_, 1, v_day_1582_);
                v___x_1586_ = l_Std_Time_ValidDate_dayOfYear(v___y_1584_, v___x_1585_);
                lean_dec_ref_known(v___x_1585_, 2);
                return v___x_1586_;
            }
            2 => {
                v___x_1591_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1592_ = lean_int_mod(v_year_1580_, v___x_1591_);
                v___x_1593_ = lean_int_dec_eq(v___x_1592_, v___x_1589_);
                lean_dec(v___x_1592_);
                v___y_1584_ = v___x_1593_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_dayOfYear___boxed(
    mut v_date_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1599_: *mut LeanObject = core::ptr::null_mut();
    v_res_1599_ = l_Std_Time_PlainDate_dayOfYear(v_date_1598_);
    lean_dec_ref(v_date_1598_);
    return v_res_1599_;
}
pub unsafe fn l_Std_Time_PlainDate_era(mut v_date_1600_: *mut LeanObject) -> u8 {
    let mut v_year_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u8 = 0;
    v_year_1601_ = lean_ctor_get(v_date_1600_, 0);
    v___x_1602_ = l_Std_Time_Year_Offset_era(v_year_1601_);
    return v___x_1602_;
}
pub unsafe fn l_Std_Time_PlainDate_era___boxed(
    mut v_date_1603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1604_: u8 = 0;
    let mut v_r_1605_: *mut LeanObject = core::ptr::null_mut();
    v_res_1604_ = l_Std_Time_PlainDate_era(v_date_1603_);
    lean_dec_ref(v_date_1603_);
    v_r_1605_ = lean_box((v_res_1604_) as usize);
    return v_r_1605_;
}
pub unsafe fn l_Std_Time_PlainDate_inLeapYear(mut v_date_1606_: *mut LeanObject) -> u8 {
    let mut v_year_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: u8 = 0;
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1607_ = lean_ctor_get(v_date_1606_, 0);
                v___x_1608_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1609_ = lean_int_mod(v_year_1607_, v___x_1608_);
                v___x_1610_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1615_ = lean_int_dec_eq(v___x_1609_, v___x_1610_);
                lean_dec(v___x_1609_);
                if v___x_1615_ == 0 {
                    return v___x_1615_;
                } else {
                    v___x_1616_ = lean_obj_once(
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
                    lean_dec(v___x_1617_);
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
                v___x_1612_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1613_ = lean_int_mod(v_year_1607_, v___x_1612_);
                v___x_1614_ = lean_int_dec_eq(v___x_1613_, v___x_1610_);
                lean_dec(v___x_1613_);
                return v___x_1614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_inLeapYear___boxed(
    mut v_date_1619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1620_: u8 = 0;
    let mut v_r_1621_: *mut LeanObject = core::ptr::null_mut();
    v_res_1620_ = l_Std_Time_PlainDate_inLeapYear(v_date_1619_);
    lean_dec_ref(v_date_1619_);
    v_r_1621_ = lean_box((v_res_1620_) as usize);
    return v_r_1621_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_toEpochDay___closed__0() -> *mut LeanObject {
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    v___x_1622_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__13_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__13,
    );
    v___x_1623_ = lean_int_neg(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_toEpochDay___closed__1() -> *mut LeanObject {
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    v___x_1624_ = lean_unsigned_to_nat(399);
    v___x_1625_ = lean_nat_to_int(v___x_1624_);
    return v___x_1625_;
}
pub unsafe fn l_Std_Time_PlainDate_toEpochDay(
    mut v_date_1626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doy_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doe_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_era_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_yoe_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1627_ = lean_ctor_get(v_date_1626_, 0);
                lean_inc(v_year_1627_);
                v_month_1628_ = lean_ctor_get(v_date_1626_, 1);
                lean_inc(v_month_1628_);
                v_day_1629_ = lean_ctor_get(v_date_1626_, 2);
                lean_inc(v_day_1629_);
                lean_dec_ref(v_date_1626_);
                v___x_1630_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__9_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__9,
                );
                v___x_1631_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1675_ = lean_int_dec_lt(v___x_1630_, v_month_1628_);
                if v___x_1675_ == 0 {
                    v___x_1676_ = lean_int_sub(v_year_1627_, v___x_1631_);
                    lean_dec(v_year_1627_);
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
                lean_dec(v_month_1628_);
                v___x_1638_ = lean_int_mul(v___y_1635_, v___x_1637_);
                lean_dec(v___x_1637_);
                v___x_1639_ = lean_int_add(v___x_1638_, v___x_1630_);
                lean_dec(v___x_1638_);
                v___x_1640_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__8,
                );
                v___x_1641_ = lean_int_div(v___x_1639_, v___x_1640_);
                lean_dec(v___x_1639_);
                v___x_1642_ = lean_int_add(v___x_1641_, v_day_1629_);
                lean_dec(v_day_1629_);
                lean_dec(v___x_1641_);
                v_doy_1643_ = lean_int_sub(v___x_1642_, v___x_1631_);
                lean_dec(v___x_1642_);
                v___x_1644_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__7_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__7,
                );
                v___x_1645_ = lean_int_mul(v___y_1633_, v___x_1644_);
                v___x_1646_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1647_ = lean_int_div(v___y_1633_, v___x_1646_);
                v___x_1648_ = lean_int_add(v___x_1645_, v___x_1647_);
                lean_dec(v___x_1647_);
                lean_dec(v___x_1645_);
                v___x_1649_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__2,
                );
                v___x_1650_ = lean_int_div(v___y_1633_, v___x_1649_);
                lean_dec(v___y_1633_);
                v___x_1651_ = lean_int_sub(v___x_1648_, v___x_1650_);
                lean_dec(v___x_1650_);
                lean_dec(v___x_1648_);
                v_doe_1652_ = lean_int_add(v___x_1651_, v_doy_1643_);
                lean_dec(v_doy_1643_);
                lean_dec(v___x_1651_);
                v___x_1653_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__3_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__3,
                );
                v___x_1654_ = lean_int_mul(v___y_1634_, v___x_1653_);
                lean_dec(v___y_1634_);
                v___x_1655_ = lean_int_add(v___x_1654_, v_doe_1652_);
                lean_dec(v_doe_1652_);
                lean_dec(v___x_1654_);
                v___x_1656_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__0_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__0,
                );
                v___x_1657_ = lean_int_sub(v___x_1655_, v___x_1656_);
                lean_dec(v___x_1655_);
                return v___x_1657_;
            }
            2 => {
                v___x_1661_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v_era_1662_ = lean_int_div(v___y_1660_, v___x_1661_);
                lean_dec(v___y_1660_);
                v___x_1663_ = lean_int_mul(v_era_1662_, v___x_1661_);
                v_yoe_1664_ = lean_int_sub(v___y_1659_, v___x_1663_);
                lean_dec(v___x_1663_);
                lean_dec(v___y_1659_);
                v___x_1665_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__10_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__10,
                );
                v___x_1666_ = lean_int_dec_lt(v___x_1630_, v_month_1628_);
                if v___x_1666_ == 0 {
                    v___x_1667_ = lean_obj_once(
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
                    v___x_1668_ = lean_obj_once(
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
                v___x_1671_ = lean_obj_once(
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
                    v___x_1673_ = lean_obj_once(
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
                    lean_inc(v___y_1670_);
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
    mut v_date_1677_: *mut LeanObject,
    mut v_days_1678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dateDays_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    v_dateDays_1679_ = l_Std_Time_PlainDate_toEpochDay(v_date_1677_);
    v___x_1680_ = lean_int_add(v_dateDays_1679_, v_days_1678_);
    lean_dec(v_dateDays_1679_);
    v___x_1681_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1680_);
    lean_dec(v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Std_Time_PlainDate_addDays___boxed(
    mut v_date_1682_: *mut LeanObject,
    mut v_days_1683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1684_: *mut LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Std_Time_PlainDate_addDays(v_date_1682_, v_days_1683_);
    lean_dec(v_days_1683_);
    return v_res_1684_;
}
pub unsafe fn l_Std_Time_PlainDate_subDays(
    mut v_date_1685_: *mut LeanObject,
    mut v_days_1686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    v___x_1687_ = lean_int_neg(v_days_1686_);
    v_dateDays_1688_ = l_Std_Time_PlainDate_toEpochDay(v_date_1685_);
    v___x_1689_ = lean_int_add(v_dateDays_1688_, v___x_1687_);
    lean_dec(v___x_1687_);
    lean_dec(v_dateDays_1688_);
    v___x_1690_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1689_);
    lean_dec(v___x_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Std_Time_PlainDate_subDays___boxed(
    mut v_date_1691_: *mut LeanObject,
    mut v_days_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Std_Time_PlainDate_subDays(v_date_1691_, v_days_1692_);
    lean_dec(v_days_1692_);
    return v_res_1693_;
}
pub unsafe fn l_Std_Time_PlainDate_addWeeks(
    mut v_date_1694_: *mut LeanObject,
    mut v_weeks_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dateDays_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    v_dateDays_1696_ = l_Std_Time_PlainDate_toEpochDay(v_date_1694_);
    v___x_1697_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v_daysToAdd_1698_ = lean_int_mul(v_weeks_1695_, v___x_1697_);
    v___x_1699_ = lean_int_add(v_dateDays_1696_, v_daysToAdd_1698_);
    lean_dec(v_daysToAdd_1698_);
    lean_dec(v_dateDays_1696_);
    v___x_1700_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1699_);
    lean_dec(v___x_1699_);
    return v___x_1700_;
}
pub unsafe fn l_Std_Time_PlainDate_addWeeks___boxed(
    mut v_date_1701_: *mut LeanObject,
    mut v_weeks_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Std_Time_PlainDate_addWeeks(v_date_1701_, v_weeks_1702_);
    lean_dec(v_weeks_1702_);
    return v_res_1703_;
}
pub unsafe fn l_Std_Time_PlainDate_subWeeks(
    mut v_date_1704_: *mut LeanObject,
    mut v_weeks_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = lean_int_neg(v_weeks_1705_);
    v_dateDays_1707_ = l_Std_Time_PlainDate_toEpochDay(v_date_1704_);
    v___x_1708_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v_daysToAdd_1709_ = lean_int_mul(v___x_1706_, v___x_1708_);
    lean_dec(v___x_1706_);
    v___x_1710_ = lean_int_add(v_dateDays_1707_, v_daysToAdd_1709_);
    lean_dec(v_daysToAdd_1709_);
    lean_dec(v_dateDays_1707_);
    v___x_1711_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1710_);
    lean_dec(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn l_Std_Time_PlainDate_subWeeks___boxed(
    mut v_date_1712_: *mut LeanObject,
    mut v_weeks_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1714_: *mut LeanObject = core::ptr::null_mut();
    v_res_1714_ = l_Std_Time_PlainDate_subWeeks(v_date_1712_, v_weeks_1713_);
    lean_dec(v_weeks_1713_);
    return v_res_1714_;
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsClip(
    mut v_date_1715_: *mut LeanObject,
    mut v_months_1716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1722_: u8 = 0;
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_totalMonths_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wrappedMonths_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_yearsOffset_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1732_: u8 = 0;
    let mut v_max_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: u8 = 0;
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: u8 = 0;
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1717_ = lean_ctor_get(v_date_1715_, 0);
                v_month_1718_ = lean_ctor_get(v_date_1715_, 1);
                v_day_1719_ = lean_ctor_get(v_date_1715_, 2);
                v_isSharedCheck_1752_ = (!lean_is_exclusive(v_date_1715_)) as u8;
                if v_isSharedCheck_1752_ == 0 {
                    v___x_1721_ = v_date_1715_;
                    v_isShared_1722_ = v_isSharedCheck_1752_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_day_1719_);
                    lean_inc(v_month_1718_);
                    lean_inc(v_year_1717_);
                    lean_dec(v_date_1715_);
                    v___x_1721_ = lean_box(0);
                    v_isShared_1722_ = v_isSharedCheck_1752_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1723_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1724_ = lean_int_sub(v_month_1718_, v___x_1723_);
                lean_dec(v_month_1718_);
                v_totalMonths_1725_ = lean_int_add(v___x_1724_, v_months_1716_);
                lean_dec(v___x_1724_);
                v___x_1726_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
                    _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
                );
                v___x_1727_ = lean_int_emod(v_totalMonths_1725_, v___x_1726_);
                v_wrappedMonths_1728_ = lean_int_add(v___x_1727_, v___x_1723_);
                lean_dec(v___x_1727_);
                v_yearsOffset_1729_ = lean_int_ediv(v_totalMonths_1725_, v___x_1726_);
                lean_dec(v_totalMonths_1725_);
                v___x_1730_ = lean_int_add(v_year_1717_, v_yearsOffset_1729_);
                lean_dec(v_yearsOffset_1729_);
                lean_dec(v_year_1717_);
                v___x_1741_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1742_ = lean_int_mod(v___x_1730_, v___x_1741_);
                v___x_1743_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1748_ = lean_int_dec_eq(v___x_1742_, v___x_1743_);
                lean_dec(v___x_1742_);
                if v___x_1748_ == 0 {
                    v___y_1732_ = v___x_1748_;
                    state = 2;
                    continue;
                } else {
                    v___x_1749_ = lean_obj_once(
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
                    lean_dec(v___x_1750_);
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
                    lean_dec(v_max_1733_);
                    if v_isShared_1722_ == 0 {
                        lean_ctor_set(v___x_1721_, 1, v_wrappedMonths_1728_);
                        lean_ctor_set(v___x_1721_, 0, v___x_1730_);
                        v___x_1736_ = v___x_1721_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1730_);
                        lean_ctor_set(v_reuseFailAlloc_1737_, 1, v_wrappedMonths_1728_);
                        lean_ctor_set(v_reuseFailAlloc_1737_, 2, v_day_1719_);
                        v___x_1736_ = v_reuseFailAlloc_1737_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_day_1719_);
                    if v_isShared_1722_ == 0 {
                        lean_ctor_set(v___x_1721_, 2, v_max_1733_);
                        lean_ctor_set(v___x_1721_, 1, v_wrappedMonths_1728_);
                        lean_ctor_set(v___x_1721_, 0, v___x_1730_);
                        v___x_1739_ = v___x_1721_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1730_);
                        lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_wrappedMonths_1728_);
                        lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_max_1733_);
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
                v___x_1745_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1746_ = lean_int_mod(v___x_1730_, v___x_1745_);
                v___x_1747_ = lean_int_dec_eq(v___x_1746_, v___x_1743_);
                lean_dec(v___x_1746_);
                v___y_1732_ = v___x_1747_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsClip___boxed(
    mut v_date_1753_: *mut LeanObject,
    mut v_months_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1755_: *mut LeanObject = core::ptr::null_mut();
    v_res_1755_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1753_, v_months_1754_);
    lean_dec(v_months_1754_);
    return v_res_1755_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsClip(
    mut v_date_1756_: *mut LeanObject,
    mut v_months_1757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    v___x_1758_ = lean_int_neg(v_months_1757_);
    v___x_1759_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1756_, v___x_1758_);
    lean_dec(v___x_1758_);
    return v___x_1759_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsClip___boxed(
    mut v_date_1760_: *mut LeanObject,
    mut v_months_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_Std_Time_PlainDate_subMonthsClip(v_date_1760_, v_months_1761_);
    lean_dec(v_months_1761_);
    return v_res_1762_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__0() -> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    v___x_1763_ = lean_unsigned_to_nat(30);
    v___x_1764_ = lean_nat_to_int(v___x_1763_);
    return v___x_1764_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__1() -> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__0_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__0,
    );
    v___x_1766_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1767_ = lean_int_add(v___x_1766_, v___x_1765_);
    return v___x_1767_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__2() -> *mut LeanObject {
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    v___x_1768_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1769_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__1_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__1,
    );
    v___x_1770_ = lean_int_sub(v___x_1769_, v___x_1768_);
    return v___x_1770_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__3() -> *mut LeanObject {
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1773_: *mut LeanObject = core::ptr::null_mut();
    v___x_1771_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1772_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__2_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__2,
    );
    v_range_1773_ = lean_int_add(v___x_1772_, v___x_1771_);
    return v_range_1773_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__4() -> *mut LeanObject {
    let mut v_range_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    v_range_1774_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__3,
    );
    v___x_1775_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__5,
    );
    v___x_1776_ = lean_int_emod(v___x_1775_, v_range_1774_);
    return v___x_1776_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__5() -> *mut LeanObject {
    let mut v_range_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    v_range_1777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__3,
    );
    v___x_1778_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__4_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__4,
    );
    v___x_1779_ = lean_int_add(v___x_1778_, v_range_1777_);
    return v___x_1779_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__6() -> *mut LeanObject {
    let mut v_range_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    v_range_1780_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__3_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__3,
    );
    v___x_1781_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__5_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__5,
    );
    v___x_1782_ = lean_int_emod(v___x_1781_, v_range_1780_);
    return v___x_1782_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_rollOver___closed__7() -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    v___x_1783_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_1784_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__6_once),
        _init_l_Std_Time_PlainDate_rollOver___closed__6,
    );
    v___x_1785_ = lean_int_add(v___x_1784_, v___x_1783_);
    return v___x_1785_;
}
pub unsafe fn l_Std_Time_PlainDate_rollOver(
    mut v_year_1786_: *mut LeanObject,
    mut v_month_1787_: *mut LeanObject,
    mut v_day_1788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1798_: u8 = 0;
    let mut v_max_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: u8 = 0;
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1796_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7_once),
                    _init_l_Std_Time_PlainDate_rollOver___closed__7,
                );
                v___x_1803_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1804_ = lean_int_mod(v_year_1786_, v___x_1803_);
                v___x_1805_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1810_ = lean_int_dec_eq(v___x_1804_, v___x_1805_);
                lean_dec(v___x_1804_);
                if v___x_1810_ == 0 {
                    v___y_1798_ = v___x_1810_;
                    state = 2;
                    continue;
                } else {
                    v___x_1811_ = lean_obj_once(
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
                    lean_dec(v___x_1812_);
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
                v___x_1791_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1792_ = lean_int_sub(v_day_1788_, v___x_1791_);
                v_dateDays_1793_ = l_Std_Time_PlainDate_toEpochDay(v___y_1790_);
                v___x_1794_ = lean_int_add(v_dateDays_1793_, v___x_1792_);
                lean_dec(v___x_1792_);
                lean_dec(v_dateDays_1793_);
                v___x_1795_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1794_);
                lean_dec(v___x_1794_);
                return v___x_1795_;
            }
            2 => {
                v_max_1799_ = l_Std_Time_Month_Ordinal_days(v___y_1798_, v_month_1787_);
                v___x_1800_ = lean_int_dec_lt(v_max_1799_, v___x_1796_);
                if v___x_1800_ == 0 {
                    lean_dec(v_max_1799_);
                    v___x_1801_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1801_, 0, v_year_1786_);
                    lean_ctor_set(v___x_1801_, 1, v_month_1787_);
                    lean_ctor_set(v___x_1801_, 2, v___x_1796_);
                    v___y_1790_ = v___x_1801_;
                    state = 1;
                    continue;
                } else {
                    v___x_1802_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1802_, 0, v_year_1786_);
                    lean_ctor_set(v___x_1802_, 1, v_month_1787_);
                    lean_ctor_set(v___x_1802_, 2, v_max_1799_);
                    v___y_1790_ = v___x_1802_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1807_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1808_ = lean_int_mod(v_year_1786_, v___x_1807_);
                v___x_1809_ = lean_int_dec_eq(v___x_1808_, v___x_1805_);
                lean_dec(v___x_1808_);
                v___y_1798_ = v___x_1809_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_rollOver___boxed(
    mut v_year_1814_: *mut LeanObject,
    mut v_month_1815_: *mut LeanObject,
    mut v_day_1816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1817_: *mut LeanObject = core::ptr::null_mut();
    v_res_1817_ = l_Std_Time_PlainDate_rollOver(v_year_1814_, v_month_1815_, v_day_1816_);
    lean_dec(v_day_1816_);
    return v_res_1817_;
}
pub unsafe fn l_Std_Time_PlainDate_withYearClip(
    mut v_dt_1818_: *mut LeanObject,
    mut v_year_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_month_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___y_1826_: u8 = 0;
    let mut v_max_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut v_unused_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_month_1820_ = lean_ctor_get(v_dt_1818_, 1);
                v_day_1821_ = lean_ctor_get(v_dt_1818_, 2);
                v_isSharedCheck_1846_ = (!lean_is_exclusive(v_dt_1818_)) as u8;
                if v_isSharedCheck_1846_ == 0 {
                    v_unused_1847_ = lean_ctor_get(v_dt_1818_, 0);
                    lean_dec(v_unused_1847_);
                    v___x_1823_ = v_dt_1818_;
                    v_isShared_1824_ = v_isSharedCheck_1846_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_day_1821_);
                    lean_inc(v_month_1820_);
                    lean_dec(v_dt_1818_);
                    v___x_1823_ = lean_box(0);
                    v_isShared_1824_ = v_isSharedCheck_1846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1835_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1836_ = lean_int_mod(v_year_1819_, v___x_1835_);
                v___x_1837_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1842_ = lean_int_dec_eq(v___x_1836_, v___x_1837_);
                lean_dec(v___x_1836_);
                if v___x_1842_ == 0 {
                    v___y_1826_ = v___x_1842_;
                    state = 2;
                    continue;
                } else {
                    v___x_1843_ = lean_obj_once(
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
                    lean_dec(v___x_1844_);
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
                    lean_dec(v_max_1827_);
                    if v_isShared_1824_ == 0 {
                        lean_ctor_set(v___x_1823_, 0, v_year_1819_);
                        v___x_1830_ = v___x_1823_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_year_1819_);
                        lean_ctor_set(v_reuseFailAlloc_1831_, 1, v_month_1820_);
                        lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_day_1821_);
                        v___x_1830_ = v_reuseFailAlloc_1831_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_day_1821_);
                    if v_isShared_1824_ == 0 {
                        lean_ctor_set(v___x_1823_, 2, v_max_1827_);
                        lean_ctor_set(v___x_1823_, 0, v_year_1819_);
                        v___x_1833_ = v___x_1823_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_year_1819_);
                        lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_month_1820_);
                        lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_max_1827_);
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
                v___x_1839_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1840_ = lean_int_mod(v_year_1819_, v___x_1839_);
                v___x_1841_ = lean_int_dec_eq(v___x_1840_, v___x_1837_);
                lean_dec(v___x_1840_);
                v___y_1826_ = v___x_1841_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withYearRollOver(
    mut v_dt_1848_: *mut LeanObject,
    mut v_year_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_month_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    v_month_1850_ = lean_ctor_get(v_dt_1848_, 1);
    lean_inc(v_month_1850_);
    v_day_1851_ = lean_ctor_get(v_dt_1848_, 2);
    lean_inc(v_day_1851_);
    lean_dec_ref(v_dt_1848_);
    v___x_1852_ = l_Std_Time_PlainDate_rollOver(v_year_1849_, v_month_1850_, v_day_1851_);
    lean_dec(v_day_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsRollOver(
    mut v_date_1853_: *mut LeanObject,
    mut v_months_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1860_: u8 = 0;
    let mut v___y_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dateDays_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: u8 = 0;
    let mut v_max_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1887_: u8 = 0;
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: u8 = 0;
    let mut v_isSharedCheck_1891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1855_ = lean_ctor_get(v_date_1853_, 0);
                v_month_1856_ = lean_ctor_get(v_date_1853_, 1);
                v_day_1857_ = lean_ctor_get(v_date_1853_, 2);
                v_isSharedCheck_1891_ = (!lean_is_exclusive(v_date_1853_)) as u8;
                if v_isSharedCheck_1891_ == 0 {
                    v___x_1859_ = v_date_1853_;
                    v_isShared_1860_ = v_isSharedCheck_1891_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_day_1857_);
                    lean_inc(v_month_1856_);
                    lean_inc(v_year_1855_);
                    lean_dec(v_date_1853_);
                    v___x_1859_ = lean_box(0);
                    v_isShared_1860_ = v_isSharedCheck_1891_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1869_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7_once),
                    _init_l_Std_Time_PlainDate_rollOver___closed__7,
                );
                v___x_1880_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1881_ = lean_int_mod(v_year_1855_, v___x_1880_);
                v___x_1882_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1887_ = lean_int_dec_eq(v___x_1881_, v___x_1882_);
                lean_dec(v___x_1881_);
                if v___x_1887_ == 0 {
                    v___y_1871_ = v___x_1887_;
                    state = 3;
                    continue;
                } else {
                    v___x_1888_ = lean_obj_once(
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
                    lean_dec(v___x_1889_);
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
                v___x_1864_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_1865_ = lean_int_sub(v_day_1857_, v___x_1864_);
                lean_dec(v_day_1857_);
                v_dateDays_1866_ = l_Std_Time_PlainDate_toEpochDay(v___x_1863_);
                v___x_1867_ = lean_int_add(v_dateDays_1866_, v___x_1865_);
                lean_dec(v___x_1865_);
                lean_dec(v_dateDays_1866_);
                v___x_1868_ = l_Std_Time_PlainDate_ofEpochDay(v___x_1867_);
                lean_dec(v___x_1867_);
                return v___x_1868_;
            }
            3 => {
                v_max_1872_ = l_Std_Time_Month_Ordinal_days(v___y_1871_, v_month_1856_);
                v___x_1873_ = lean_int_dec_lt(v_max_1872_, v___x_1869_);
                if v___x_1873_ == 0 {
                    lean_dec(v_max_1872_);
                    if v_isShared_1860_ == 0 {
                        lean_ctor_set(v___x_1859_, 2, v___x_1869_);
                        v___x_1875_ = v___x_1859_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_year_1855_);
                        lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_month_1856_);
                        lean_ctor_set(v_reuseFailAlloc_1876_, 2, v___x_1869_);
                        v___x_1875_ = v_reuseFailAlloc_1876_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_1860_ == 0 {
                        lean_ctor_set(v___x_1859_, 2, v_max_1872_);
                        v___x_1878_ = v___x_1859_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_year_1855_);
                        lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_month_1856_);
                        lean_ctor_set(v_reuseFailAlloc_1879_, 2, v_max_1872_);
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
                v___x_1884_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1885_ = lean_int_mod(v_year_1855_, v___x_1884_);
                v___x_1886_ = lean_int_dec_eq(v___x_1885_, v___x_1882_);
                lean_dec(v___x_1885_);
                v___y_1871_ = v___x_1886_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_addMonthsRollOver___boxed(
    mut v_date_1892_: *mut LeanObject,
    mut v_months_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1894_: *mut LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1892_, v_months_1893_);
    lean_dec(v_months_1893_);
    return v_res_1894_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsRollOver(
    mut v_date_1895_: *mut LeanObject,
    mut v_months_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    v___x_1897_ = lean_int_neg(v_months_1896_);
    v___x_1898_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1895_, v___x_1897_);
    lean_dec(v___x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Std_Time_PlainDate_subMonthsRollOver___boxed(
    mut v_date_1899_: *mut LeanObject,
    mut v_months_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1901_: *mut LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_Std_Time_PlainDate_subMonthsRollOver(v_date_1899_, v_months_1900_);
    lean_dec(v_months_1900_);
    return v_res_1901_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsRollOver(
    mut v_date_1902_: *mut LeanObject,
    mut v_years_1903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    v___x_1904_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1905_ = lean_int_mul(v_years_1903_, v___x_1904_);
    v___x_1906_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1902_, v___x_1905_);
    lean_dec(v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsRollOver___boxed(
    mut v_date_1907_: *mut LeanObject,
    mut v_years_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1909_: *mut LeanObject = core::ptr::null_mut();
    v_res_1909_ = l_Std_Time_PlainDate_addYearsRollOver(v_date_1907_, v_years_1908_);
    lean_dec(v_years_1908_);
    return v_res_1909_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsRollOver(
    mut v_date_1910_: *mut LeanObject,
    mut v_years_1911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1913_ = lean_int_mul(v_years_1911_, v___x_1912_);
    v___x_1914_ = lean_int_neg(v___x_1913_);
    lean_dec(v___x_1913_);
    v___x_1915_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_1910_, v___x_1914_);
    lean_dec(v___x_1914_);
    return v___x_1915_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsRollOver___boxed(
    mut v_date_1916_: *mut LeanObject,
    mut v_years_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1918_: *mut LeanObject = core::ptr::null_mut();
    v_res_1918_ = l_Std_Time_PlainDate_subYearsRollOver(v_date_1916_, v_years_1917_);
    lean_dec(v_years_1917_);
    return v_res_1918_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsClip(
    mut v_date_1919_: *mut LeanObject,
    mut v_years_1920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    v___x_1921_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1922_ = lean_int_mul(v_years_1920_, v___x_1921_);
    v___x_1923_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1919_, v___x_1922_);
    lean_dec(v___x_1922_);
    return v___x_1923_;
}
pub unsafe fn l_Std_Time_PlainDate_addYearsClip___boxed(
    mut v_date_1924_: *mut LeanObject,
    mut v_years_1925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1926_: *mut LeanObject = core::ptr::null_mut();
    v_res_1926_ = l_Std_Time_PlainDate_addYearsClip(v_date_1924_, v_years_1925_);
    lean_dec(v_years_1925_);
    return v_res_1926_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsClip(
    mut v_date_1927_: *mut LeanObject,
    mut v_years_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    v___x_1929_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__2_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__2,
    );
    v___x_1930_ = lean_int_mul(v_years_1928_, v___x_1929_);
    v___x_1931_ = lean_int_neg(v___x_1930_);
    lean_dec(v___x_1930_);
    v___x_1932_ = l_Std_Time_PlainDate_addMonthsClip(v_date_1927_, v___x_1931_);
    lean_dec(v___x_1931_);
    return v___x_1932_;
}
pub unsafe fn l_Std_Time_PlainDate_subYearsClip___boxed(
    mut v_date_1933_: *mut LeanObject,
    mut v_years_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1935_: *mut LeanObject = core::ptr::null_mut();
    v_res_1935_ = l_Std_Time_PlainDate_subYearsClip(v_date_1933_, v_years_1934_);
    lean_dec(v_years_1934_);
    return v_res_1935_;
}
pub unsafe fn l_Std_Time_PlainDate_withDaysClip(
    mut v_dt_1936_: *mut LeanObject,
    mut v_days_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1942_: u8 = 0;
    let mut v___y_1944_: u8 = 0;
    let mut v_max_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v_isSharedCheck_1964_: u8 = 0;
    let mut v_unused_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1938_ = lean_ctor_get(v_dt_1936_, 0);
                v_month_1939_ = lean_ctor_get(v_dt_1936_, 1);
                v_isSharedCheck_1964_ = (!lean_is_exclusive(v_dt_1936_)) as u8;
                if v_isSharedCheck_1964_ == 0 {
                    v_unused_1965_ = lean_ctor_get(v_dt_1936_, 2);
                    lean_dec(v_unused_1965_);
                    v___x_1941_ = v_dt_1936_;
                    v_isShared_1942_ = v_isSharedCheck_1964_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_month_1939_);
                    lean_inc(v_year_1938_);
                    lean_dec(v_dt_1936_);
                    v___x_1941_ = lean_box(0);
                    v_isShared_1942_ = v_isSharedCheck_1964_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1953_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1954_ = lean_int_mod(v_year_1938_, v___x_1953_);
                v___x_1955_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1960_ = lean_int_dec_eq(v___x_1954_, v___x_1955_);
                lean_dec(v___x_1954_);
                if v___x_1960_ == 0 {
                    v___y_1944_ = v___x_1960_;
                    state = 2;
                    continue;
                } else {
                    v___x_1961_ = lean_obj_once(
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
                    lean_dec(v___x_1962_);
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
                    lean_dec(v_max_1945_);
                    if v_isShared_1942_ == 0 {
                        lean_ctor_set(v___x_1941_, 2, v_days_1937_);
                        v___x_1948_ = v___x_1941_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_year_1938_);
                        lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_month_1939_);
                        lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_days_1937_);
                        v___x_1948_ = v_reuseFailAlloc_1949_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_days_1937_);
                    if v_isShared_1942_ == 0 {
                        lean_ctor_set(v___x_1941_, 2, v_max_1945_);
                        v___x_1951_ = v___x_1941_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1952_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_year_1938_);
                        lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_month_1939_);
                        lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_max_1945_);
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
                v___x_1957_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1958_ = lean_int_mod(v_year_1938_, v___x_1957_);
                v___x_1959_ = lean_int_dec_eq(v___x_1958_, v___x_1955_);
                lean_dec(v___x_1958_);
                v___y_1944_ = v___x_1959_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withDaysRollOver(
    mut v_dt_1966_: *mut LeanObject,
    mut v_days_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    v_year_1968_ = lean_ctor_get(v_dt_1966_, 0);
    lean_inc(v_year_1968_);
    v_month_1969_ = lean_ctor_get(v_dt_1966_, 1);
    lean_inc(v_month_1969_);
    lean_dec_ref(v_dt_1966_);
    v___x_1970_ = l_Std_Time_PlainDate_rollOver(v_year_1968_, v_month_1969_, v_days_1967_);
    return v___x_1970_;
}
pub unsafe fn l_Std_Time_PlainDate_withDaysRollOver___boxed(
    mut v_dt_1971_: *mut LeanObject,
    mut v_days_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1973_: *mut LeanObject = core::ptr::null_mut();
    v_res_1973_ = l_Std_Time_PlainDate_withDaysRollOver(v_dt_1971_, v_days_1972_);
    lean_dec(v_days_1972_);
    return v_res_1973_;
}
pub unsafe fn l_Std_Time_PlainDate_withMonthClip(
    mut v_dt_1974_: *mut LeanObject,
    mut v_month_1975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1980_: u8 = 0;
    let mut v___y_1982_: u8 = 0;
    let mut v_max_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u8 = 0;
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: u8 = 0;
    let mut v_isSharedCheck_2002_: u8 = 0;
    let mut v_unused_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_1976_ = lean_ctor_get(v_dt_1974_, 0);
                v_day_1977_ = lean_ctor_get(v_dt_1974_, 2);
                v_isSharedCheck_2002_ = (!lean_is_exclusive(v_dt_1974_)) as u8;
                if v_isSharedCheck_2002_ == 0 {
                    v_unused_2003_ = lean_ctor_get(v_dt_1974_, 1);
                    lean_dec(v_unused_2003_);
                    v___x_1979_ = v_dt_1974_;
                    v_isShared_1980_ = v_isSharedCheck_2002_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_day_1977_);
                    lean_inc(v_year_1976_);
                    lean_dec(v_dt_1974_);
                    v___x_1979_ = lean_box(0);
                    v_isShared_1980_ = v_isSharedCheck_2002_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1991_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_1992_ = lean_int_mod(v_year_1976_, v___x_1991_);
                v___x_1993_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_1998_ = lean_int_dec_eq(v___x_1992_, v___x_1993_);
                lean_dec(v___x_1992_);
                if v___x_1998_ == 0 {
                    v___y_1982_ = v___x_1998_;
                    state = 2;
                    continue;
                } else {
                    v___x_1999_ = lean_obj_once(
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
                    lean_dec(v___x_2000_);
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
                    lean_dec(v_max_1983_);
                    if v_isShared_1980_ == 0 {
                        lean_ctor_set(v___x_1979_, 1, v_month_1975_);
                        v___x_1986_ = v___x_1979_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_year_1976_);
                        lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_month_1975_);
                        lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_day_1977_);
                        v___x_1986_ = v_reuseFailAlloc_1987_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_day_1977_);
                    if v_isShared_1980_ == 0 {
                        lean_ctor_set(v___x_1979_, 2, v_max_1983_);
                        lean_ctor_set(v___x_1979_, 1, v_month_1975_);
                        v___x_1989_ = v___x_1979_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_year_1976_);
                        lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_month_1975_);
                        lean_ctor_set(v_reuseFailAlloc_1990_, 2, v_max_1983_);
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
                v___x_1995_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_1996_ = lean_int_mod(v_year_1976_, v___x_1995_);
                v___x_1997_ = lean_int_dec_eq(v___x_1996_, v___x_1993_);
                lean_dec(v___x_1996_);
                v___y_1982_ = v___x_1997_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withMonthRollOver(
    mut v_dt_2004_: *mut LeanObject,
    mut v_month_2005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_year_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    v_year_2006_ = lean_ctor_get(v_dt_2004_, 0);
    lean_inc(v_year_2006_);
    v_day_2007_ = lean_ctor_get(v_dt_2004_, 2);
    lean_inc(v_day_2007_);
    lean_dec_ref(v_dt_2004_);
    v___x_2008_ = l_Std_Time_PlainDate_rollOver(v_year_2006_, v_month_2005_, v_day_2007_);
    lean_dec(v_day_2007_);
    return v___x_2008_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__0() -> *mut LeanObject {
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    v___x_2009_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2010_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    v___x_2011_ = lean_int_sub(v___x_2010_, v___x_2009_);
    return v___x_2011_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__1() -> *mut LeanObject {
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_2014_: *mut LeanObject = core::ptr::null_mut();
    v___x_2012_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2013_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__0_once),
        _init_l_Std_Time_PlainDate_weekday___closed__0,
    );
    v_range_2014_ = lean_int_add(v___x_2013_, v___x_2012_);
    return v_range_2014_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__2() -> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once),
        _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
    );
    v___x_2016_ = lean_int_neg(v___x_2015_);
    return v___x_2016_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_weekday___closed__3() -> *mut LeanObject {
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    v___x_2017_ = lean_unsigned_to_nat(6);
    v___x_2018_ = lean_nat_to_int(v___x_2017_);
    return v___x_2018_;
}
pub unsafe fn l_Std_Time_PlainDate_weekday(mut v_date_2019_: *mut LeanObject) -> u8 {
    let mut v___y_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: u8 = 0;
    let mut v_days_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_days_2030_ = l_Std_Time_PlainDate_toEpochDay(v_date_2019_);
                v___x_2031_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_2032_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__2_once),
                    _init_l_Std_Time_PlainDate_weekday___closed__2,
                );
                v___x_2033_ = lean_int_dec_le(v___x_2032_, v_days_2030_);
                if v___x_2033_ == 0 {
                    v___x_2034_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__8_once),
                        _init_l_Std_Time_PlainDate_ofEpochDay___closed__8,
                    );
                    v___x_2035_ = lean_int_add(v_days_2030_, v___x_2034_);
                    lean_dec(v_days_2030_);
                    v___x_2036_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                        ),
                        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                    );
                    v___x_2037_ = lean_int_emod(v___x_2035_, v___x_2036_);
                    lean_dec(v___x_2035_);
                    v___x_2038_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3),
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3_once),
                        _init_l_Std_Time_PlainDate_weekday___closed__3,
                    );
                    v___x_2039_ = lean_int_add(v___x_2037_, v___x_2038_);
                    lean_dec(v___x_2037_);
                    v___y_2021_ = v___x_2039_;
                    state = 1;
                    continue;
                } else {
                    v___x_2040_ = lean_int_add(v_days_2030_, v___x_2031_);
                    lean_dec(v_days_2030_);
                    v___x_2041_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                        ),
                        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                    );
                    v___x_2042_ = lean_int_emod(v___x_2040_, v___x_2041_);
                    lean_dec(v___x_2040_);
                    v___y_2021_ = v___x_2042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2022_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v_range_2023_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1_once),
                    _init_l_Std_Time_PlainDate_weekday___closed__1,
                );
                v___x_2024_ = lean_int_sub(v___y_2021_, v___x_2022_);
                lean_dec(v___y_2021_);
                v___x_2025_ = lean_int_emod(v___x_2024_, v_range_2023_);
                lean_dec(v___x_2024_);
                v___x_2026_ = lean_int_add(v___x_2025_, v_range_2023_);
                lean_dec(v___x_2025_);
                v___x_2027_ = lean_int_emod(v___x_2026_, v_range_2023_);
                lean_dec(v___x_2026_);
                v___x_2028_ = lean_int_add(v___x_2027_, v___x_2022_);
                lean_dec(v___x_2027_);
                v___x_2029_ = l_Std_Time_Weekday_ofOrdinal(v___x_2028_);
                lean_dec(v___x_2028_);
                return v___x_2029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_weekday___boxed(
    mut v_date_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2044_: u8 = 0;
    let mut v_r_2045_: *mut LeanObject = core::ptr::null_mut();
    v_res_2044_ = l_Std_Time_PlainDate_weekday(v_date_2043_);
    v_r_2045_ = lean_box((v_res_2044_) as usize);
    return v_r_2045_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0() -> *mut LeanObject {
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    v___x_2046_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2047_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__3_once),
        _init_l_Std_Time_PlainDate_weekday___closed__3,
    );
    v___x_2048_ = lean_int_sub(v___x_2047_, v___x_2046_);
    return v___x_2048_;
}
pub unsafe fn _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1() -> *mut LeanObject {
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_2051_: *mut LeanObject = core::ptr::null_mut();
    v___x_2049_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2050_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0_once),
        _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__0,
    );
    v_range_2051_ = lean_int_add(v___x_2050_, v___x_2049_);
    return v_range_2051_;
}
pub unsafe fn l_Std_Time_PlainDate_alignedWeekOfMonth(
    mut v_date_2052_: *mut LeanObject,
    mut v_firstDay_2053_: u8,
) -> *mut LeanObject {
    let mut v_year_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___y_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: u8 = 0;
    let mut v_day1Ord_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2082_: u8 = 0;
    let mut v_max_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: u8 = 0;
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: u8 = 0;
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_year_2054_ = lean_ctor_get(v_date_2052_, 0);
                v_month_2055_ = lean_ctor_get(v_date_2052_, 1);
                v_day_2056_ = lean_ctor_get(v_date_2052_, 2);
                v_isSharedCheck_2102_ = (!lean_is_exclusive(v_date_2052_)) as u8;
                if v_isSharedCheck_2102_ == 0 {
                    v___x_2058_ = v_date_2052_;
                    v_isShared_2059_ = v_isSharedCheck_2102_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_day_2056_);
                    lean_inc(v_month_2055_);
                    lean_inc(v_year_2054_);
                    lean_dec(v_date_2052_);
                    v___x_2058_ = lean_box(0);
                    v_isShared_2059_ = v_isSharedCheck_2102_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2080_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_rollOver___closed__7_once),
                    _init_l_Std_Time_PlainDate_rollOver___closed__7,
                );
                v___x_2091_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__0,
                );
                v___x_2092_ = lean_int_mod(v_year_2054_, v___x_2091_);
                v___x_2093_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__25_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__25,
                );
                v___x_2098_ = lean_int_dec_eq(v___x_2092_, v___x_2093_);
                lean_dec(v___x_2092_);
                if v___x_2098_ == 0 {
                    v___y_2082_ = v___x_2098_;
                    state = 3;
                    continue;
                } else {
                    v___x_2099_ = lean_obj_once(
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
                    lean_dec(v___x_2100_);
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
                lean_dec(v___x_2064_);
                lean_dec(v_day1Ord_2063_);
                v___x_2066_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                    ),
                    _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                );
                v___x_2067_ = lean_int_add(v___x_2065_, v___x_2066_);
                lean_dec(v___x_2065_);
                v_offset_2068_ = lean_int_emod(v___x_2067_, v___x_2066_);
                lean_dec(v___x_2067_);
                v___x_2069_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
                    _init_l_Std_Time_instInhabitedPlainDate___closed__0,
                );
                v___x_2070_ = lean_int_sub(v_day_2056_, v___x_2069_);
                lean_dec(v_day_2056_);
                v___x_2071_ = lean_int_add(v___x_2070_, v_offset_2068_);
                lean_dec(v_offset_2068_);
                lean_dec(v___x_2070_);
                v___x_2072_ = lean_int_ediv(v___x_2071_, v___x_2066_);
                lean_dec(v___x_2071_);
                v___x_2073_ = lean_int_add(v___x_2072_, v___x_2069_);
                lean_dec(v___x_2072_);
                v_range_2074_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_alignedWeekOfMonth___closed__1,
                );
                v___x_2075_ = lean_int_sub(v___x_2073_, v___x_2069_);
                lean_dec(v___x_2073_);
                v___x_2076_ = lean_int_emod(v___x_2075_, v_range_2074_);
                lean_dec(v___x_2075_);
                v___x_2077_ = lean_int_add(v___x_2076_, v_range_2074_);
                lean_dec(v___x_2076_);
                v___x_2078_ = lean_int_emod(v___x_2077_, v_range_2074_);
                lean_dec(v___x_2077_);
                v___x_2079_ = lean_int_add(v___x_2078_, v___x_2069_);
                lean_dec(v___x_2078_);
                return v___x_2079_;
            }
            3 => {
                v_max_2083_ = l_Std_Time_Month_Ordinal_days(v___y_2082_, v_month_2055_);
                v___x_2084_ = lean_int_dec_lt(v_max_2083_, v___x_2080_);
                if v___x_2084_ == 0 {
                    lean_dec(v_max_2083_);
                    if v_isShared_2059_ == 0 {
                        lean_ctor_set(v___x_2058_, 2, v___x_2080_);
                        v___x_2086_ = v___x_2058_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_year_2054_);
                        lean_ctor_set(v_reuseFailAlloc_2087_, 1, v_month_2055_);
                        lean_ctor_set(v_reuseFailAlloc_2087_, 2, v___x_2080_);
                        v___x_2086_ = v_reuseFailAlloc_2087_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_2059_ == 0 {
                        lean_ctor_set(v___x_2058_, 2, v_max_2083_);
                        v___x_2089_ = v___x_2058_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_year_2054_);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_month_2055_);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_max_2083_);
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
                v___x_2095_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDate_ofYearMonthDayClip___closed__1,
                );
                v___x_2096_ = lean_int_mod(v_year_2054_, v___x_2095_);
                v___x_2097_ = lean_int_dec_eq(v___x_2096_, v___x_2093_);
                lean_dec(v___x_2096_);
                v___y_2082_ = v___x_2097_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_alignedWeekOfMonth___boxed(
    mut v_date_2103_: *mut LeanObject,
    mut v_firstDay_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2105_: u8 = 0;
    let mut v_res_2106_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2105_ = (lean_unbox(v_firstDay_2104_) as u8);
    v_res_2106_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2103_, v_firstDay_boxed_2105_);
    return v_res_2106_;
}
pub unsafe fn l_Std_Time_PlainDate_withWeekday(
    mut v_date_2107_: *mut LeanObject,
    mut v_desiredWeekday_2108_: u8,
) -> *mut LeanObject {
    let mut v___y_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dateDays_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: u8 = 0;
    let mut v_weekday_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_date_2107_);
                v___x_2114_ = l_Std_Time_PlainDate_weekday(v_date_2107_);
                v_weekday_2115_ = l_Std_Time_Weekday_toOrdinal(v___x_2114_);
                v___x_2116_ = l_Std_Time_Weekday_toOrdinal(v_desiredWeekday_2108_);
                v___x_2117_ = lean_int_neg(v_weekday_2115_);
                lean_dec(v_weekday_2115_);
                v___x_2118_ = lean_int_add(v___x_2116_, v___x_2117_);
                lean_dec(v___x_2117_);
                lean_dec(v___x_2116_);
                v___x_2119_ = lean_obj_once(
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
                    v___x_2121_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once
                        ),
                        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
                    );
                    v___x_2122_ = lean_int_add(v___x_2118_, v___x_2121_);
                    lean_dec(v___x_2118_);
                    v___y_2110_ = v___x_2122_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dateDays_2111_ = l_Std_Time_PlainDate_toEpochDay(v_date_2107_);
                v___x_2112_ = lean_int_add(v_dateDays_2111_, v___y_2110_);
                lean_dec(v___y_2110_);
                lean_dec(v_dateDays_2111_);
                v___x_2113_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2112_);
                lean_dec(v___x_2112_);
                return v___x_2113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDate_withWeekday___boxed(
    mut v_date_2123_: *mut LeanObject,
    mut v_desiredWeekday_2124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_desiredWeekday_boxed_2125_: u8 = 0;
    let mut v_res_2126_: *mut LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_2125_ = (lean_unbox(v_desiredWeekday_2124_) as u8);
    v_res_2126_ = l_Std_Time_PlainDate_withWeekday(v_date_2123_, v_desiredWeekday_boxed_2125_);
    return v_res_2126_;
}
pub unsafe fn l_Std_Time_PlainDate_weekOfYear(
    mut v_date_2127_: *mut LeanObject,
    mut v_firstDay_2128_: u8,
) -> *mut LeanObject {
    let mut v_year_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: u8 = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_w_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: u8 = 0;
    v_year_2129_ = lean_ctor_get(v_date_2127_, 0);
    lean_inc(v_year_2129_);
    v___x_2130_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2131_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    lean_inc_ref(v_date_2127_);
    v___x_2132_ = l_Std_Time_PlainDate_weekday(v_date_2127_);
    v___x_2133_ = l_Std_Time_Weekday_toOrdinal(v___x_2132_);
    v___x_2134_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_2128_);
    v___x_2135_ = lean_int_sub(v___x_2133_, v___x_2134_);
    lean_dec(v___x_2134_);
    lean_dec(v___x_2133_);
    v___x_2136_ = lean_int_add(v___x_2135_, v___x_2131_);
    lean_dec(v___x_2135_);
    v___x_2137_ = lean_int_emod(v___x_2136_, v___x_2131_);
    lean_dec(v___x_2136_);
    v___x_2138_ = lean_int_add(v___x_2137_, v___x_2130_);
    lean_dec(v___x_2137_);
    v_range_2139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1_once),
        _init_l_Std_Time_PlainDate_weekday___closed__1,
    );
    v___x_2140_ = lean_int_sub(v___x_2138_, v___x_2130_);
    lean_dec(v___x_2138_);
    v___x_2141_ = lean_int_emod(v___x_2140_, v_range_2139_);
    lean_dec(v___x_2140_);
    v___x_2142_ = lean_int_add(v___x_2141_, v_range_2139_);
    lean_dec(v___x_2141_);
    v___x_2143_ = lean_int_emod(v___x_2142_, v_range_2139_);
    lean_dec(v___x_2142_);
    v___x_2144_ = lean_int_add(v___x_2143_, v___x_2130_);
    lean_dec(v___x_2143_);
    v___x_2145_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__11,
    );
    v___x_2146_ = l_Std_Time_PlainDate_dayOfYear(v_date_2127_);
    lean_dec_ref(v_date_2127_);
    v___x_2147_ = lean_int_add(v___x_2145_, v___x_2146_);
    lean_dec(v___x_2146_);
    v___x_2148_ = lean_int_neg(v___x_2144_);
    lean_dec(v___x_2144_);
    v___x_2149_ = lean_int_add(v___x_2147_, v___x_2148_);
    lean_dec(v___x_2148_);
    lean_dec(v___x_2147_);
    v_w_2150_ = lean_int_ediv(v___x_2149_, v___x_2131_);
    lean_dec(v___x_2149_);
    v___x_2151_ = lean_int_dec_lt(v_w_2150_, v___x_2130_);
    if v___x_2151_ == 0 {
        let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2153_: u8 = 0;
        v___x_2152_ = l_Std_Time_Year_Offset_weeks(v_year_2129_);
        lean_dec(v_year_2129_);
        v___x_2153_ = lean_int_dec_lt(v___x_2152_, v_w_2150_);
        lean_dec(v___x_2152_);
        if v___x_2153_ == 0 {
            return v_w_2150_;
        } else {
            lean_dec(v_w_2150_);
            return v___x_2130_;
        }
    } else {
        let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_w_2150_);
        v___x_2154_ = lean_int_sub(v_year_2129_, v___x_2130_);
        lean_dec(v_year_2129_);
        v___x_2155_ = l_Std_Time_Year_Offset_weeks(v___x_2154_);
        lean_dec(v___x_2154_);
        return v___x_2155_;
    }
}
pub unsafe fn l_Std_Time_PlainDate_weekOfYear___boxed(
    mut v_date_2156_: *mut LeanObject,
    mut v_firstDay_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2158_: u8 = 0;
    let mut v_res_2159_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2158_ = (lean_unbox(v_firstDay_2157_) as u8);
    v_res_2159_ = l_Std_Time_PlainDate_weekOfYear(v_date_2156_, v_firstDay_boxed_2158_);
    return v_res_2159_;
}
pub unsafe fn l_Std_Time_PlainDate_weekYear(
    mut v_date_2160_: *mut LeanObject,
    mut v_firstDay_2161_: u8,
) -> *mut LeanObject {
    let mut v_year_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    v_year_2162_ = lean_ctor_get(v_date_2160_, 0);
    lean_inc(v_year_2162_);
    v___x_2163_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDate___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDate___closed__0,
    );
    v___x_2164_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDate_repr___redArg___closed__8_once),
        _init_l_Std_Time_instReprPlainDate_repr___redArg___closed__8,
    );
    lean_inc_ref(v_date_2160_);
    v___x_2165_ = l_Std_Time_PlainDate_weekday(v_date_2160_);
    v___x_2166_ = l_Std_Time_Weekday_toOrdinal(v___x_2165_);
    v___x_2167_ = l_Std_Time_Weekday_toOrdinal(v_firstDay_2161_);
    v___x_2168_ = lean_int_sub(v___x_2166_, v___x_2167_);
    lean_dec(v___x_2167_);
    lean_dec(v___x_2166_);
    v___x_2169_ = lean_int_add(v___x_2168_, v___x_2164_);
    lean_dec(v___x_2168_);
    v___x_2170_ = lean_int_emod(v___x_2169_, v___x_2164_);
    lean_dec(v___x_2169_);
    v___x_2171_ = lean_int_add(v___x_2170_, v___x_2163_);
    lean_dec(v___x_2170_);
    v_range_2172_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_weekday___closed__1_once),
        _init_l_Std_Time_PlainDate_weekday___closed__1,
    );
    v___x_2173_ = lean_int_sub(v___x_2171_, v___x_2163_);
    lean_dec(v___x_2171_);
    v___x_2174_ = lean_int_emod(v___x_2173_, v_range_2172_);
    lean_dec(v___x_2173_);
    v___x_2175_ = lean_int_add(v___x_2174_, v_range_2172_);
    lean_dec(v___x_2174_);
    v___x_2176_ = lean_int_emod(v___x_2175_, v_range_2172_);
    lean_dec(v___x_2175_);
    v___x_2177_ = lean_int_add(v___x_2176_, v___x_2163_);
    lean_dec(v___x_2176_);
    v___x_2178_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDate_ofEpochDay___closed__11_once),
        _init_l_Std_Time_PlainDate_ofEpochDay___closed__11,
    );
    v___x_2179_ = l_Std_Time_PlainDate_dayOfYear(v_date_2160_);
    lean_dec_ref(v_date_2160_);
    v___x_2180_ = lean_int_add(v___x_2178_, v___x_2179_);
    lean_dec(v___x_2179_);
    v___x_2181_ = lean_int_neg(v___x_2177_);
    lean_dec(v___x_2177_);
    v___x_2182_ = lean_int_add(v___x_2180_, v___x_2181_);
    lean_dec(v___x_2181_);
    lean_dec(v___x_2180_);
    v___x_2183_ = lean_int_ediv(v___x_2182_, v___x_2164_);
    lean_dec(v___x_2182_);
    v___x_2184_ = lean_int_dec_lt(v___x_2183_, v___x_2163_);
    if v___x_2184_ == 0 {
        let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2186_: u8 = 0;
        v___x_2185_ = l_Std_Time_Year_Offset_weeks(v_year_2162_);
        v___x_2186_ = lean_int_dec_lt(v___x_2185_, v___x_2183_);
        lean_dec(v___x_2183_);
        lean_dec(v___x_2185_);
        if v___x_2186_ == 0 {
            return v_year_2162_;
        } else {
            let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
            v___x_2187_ = lean_int_add(v_year_2162_, v___x_2163_);
            lean_dec(v_year_2162_);
            return v___x_2187_;
        }
    } else {
        let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2183_);
        v___x_2188_ = lean_int_sub(v_year_2162_, v___x_2163_);
        lean_dec(v_year_2162_);
        return v___x_2188_;
    }
}
pub unsafe fn l_Std_Time_PlainDate_weekYear___boxed(
    mut v_date_2189_: *mut LeanObject,
    mut v_firstDay_2190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2191_: u8 = 0;
    let mut v_res_2192_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2191_ = (lean_unbox(v_firstDay_2190_) as u8);
    v_res_2192_ = l_Std_Time_PlainDate_weekYear(v_date_2189_, v_firstDay_boxed_2191_);
    return v_res_2192_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_PlainDate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Month(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Year(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_instInhabitedPlainDate = _init_l_Std_Time_instInhabitedPlainDate();
    lean_mark_persistent(l_Std_Time_instInhabitedPlainDate);
    l_Std_Time_PlainDate_instInhabited = _init_l_Std_Time_PlainDate_instInhabited();
    lean_mark_persistent(l_Std_Time_PlainDate_instInhabited);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_PlainDate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Date_PlainDate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Month(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Year(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_PlainDate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_PlainDate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Date_PlainDate(builtin);
}
