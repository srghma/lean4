// Lean compiler output
// Module: Std.Time.DateTime.PlainDateTime
// Imports: Std.Time.DateTime.WallTime
use crate::r#gen::Init::Data::Fin::Basic::{l_Fin_add, l_Fin_succ___redArg};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Ord::Basic::{l_compareLex___boxed, l_compareOn___boxed};
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Std::Time::Date::PlainDate::{
    l_Std_Time_PlainDate_addMonthsClip, l_Std_Time_PlainDate_addMonthsRollOver,
    l_Std_Time_PlainDate_alignedWeekOfMonth, l_Std_Time_PlainDate_ofEpochDay,
    l_Std_Time_PlainDate_quarter, l_Std_Time_PlainDate_rollOver, l_Std_Time_PlainDate_toEpochDay,
    l_Std_Time_PlainDate_weekOfMonth, l_Std_Time_PlainDate_weekOfYear,
    l_Std_Time_PlainDate_weekYear, l_Std_Time_PlainDate_weekday, l_Std_Time_PlainDate_withWeekday,
    l_Std_Time_instDecidableEqPlainDate_decEq, l_Std_Time_instOrdPlainDate,
    l_Std_Time_instReprPlainDate_repr___redArg,
};
use crate::r#gen::Std::Time::Date::Unit::Month::l_Std_Time_Month_Ordinal_days;
use crate::r#gen::Std::Time::Date::Unit::Year::l_Std_Time_Year_Offset_era;
use crate::r#gen::Std::Time::Date::ValidDate::l_Std_Time_ValidDate_dayOfYear;
use crate::r#gen::Std::Time::DateTime::WallTime::{
    initialize_Std_Time_DateTime_WallTime, runtime_initialize_Std_Time_DateTime_WallTime,
};
use crate::r#gen::Std::Time::Duration::l_Std_Time_Duration_ofNanoseconds;
use crate::r#gen::Std::Time::Time::PlainTime::{
    l_Std_Time_PlainTime_toSeconds, l_Std_Time_instDecidableEqPlainTime_decEq,
    l_Std_Time_instOrdPlainTime, l_Std_Time_instReprPlainTime_repr___redArg,
};
use crate::r#gen::Std::Time::Time::Unit::Second::l_Std_Time_Second_instOfNatOrdinal;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{
    lean_int_div, lean_int_ediv, lean_int_emod, lean_int_mod,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_cstr_to_nat, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__7: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__18_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__29_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__30_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__30: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__31: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__32: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__33_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__33: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__34_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__34: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__35_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__35: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__36_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__36: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__37_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__37: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__38_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__38: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__39_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__39: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainDateTime_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainDateTime: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value: LeanStringObject<5> =
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
        m_data: [100, 97, 116, 101, 0],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value
        ) as *mut LeanObject],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value: LeanStringObject<2> =
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value
        ) as *mut LeanObject],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value: LeanStringObject<5> =
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
        m_data: [116, 105, 109, 101, 0],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value
        ) as *mut LeanObject],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value: LeanStringObject<3> =
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value
        ) as *mut LeanObject],
    };
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16_value)
        as *mut LeanObject;
pub static l_Std_Time_instReprPlainDateTime___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprPlainDateTime_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprPlainDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime___closed__0_value) as *mut LeanObject;
pub static mut l_Std_Time_instReprPlainDateTime: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDateTime___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDateTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDateTime___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instOrdPlainDateTime___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDateTime___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDateTime___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDateTime___closed__1_value) as *mut LeanObject;
static mut l_Std_Time_instOrdPlainDateTime___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instOrdPlainDateTime___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instOrdPlainDateTime___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instOrdPlainDateTime___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instOrdPlainDateTime___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instOrdPlainDateTime___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instOrdPlainDateTime: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_toWallTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_toWallTime___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_toWallTime___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_toWallTime___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__10: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__12: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__13_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__13: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__14: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__16_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__17: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__18: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__19: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__21_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__22: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__23: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__24: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__25: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__28: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__29_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__29: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__30: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__31: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__32_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__32: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_addWeeks___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_addYearsRollOver___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addHours___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_addHours___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addMinutes___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_PlainDateTime_addMinutes___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_addDays___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_subDays___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubOffset___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_addWeeks___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_subWeeks___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_addHours___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_subHours___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_addMinutes___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_subMinutes___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__3: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_addMilliseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_subMilliseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_addSeconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_subSeconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__5: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_addNanoseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_subNanoseconds___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__6: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value)
        as *mut LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_PlainDateTime_instHAddDuration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value)
        as *mut LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddDuration: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedPlainDateTime_default_spec__0(
    mut v_a_1489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    v___x_1490_ = lean_nat_to_int(v_a_1489_);
    return v___x_1490_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0() -> *mut LeanObject {
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1491_ = lean_unsigned_to_nat(0);
    v___x_1492_ = lean_nat_to_int(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1() -> *mut LeanObject {
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493_ = lean_unsigned_to_nat(1);
    v___x_1494_ = lean_nat_to_int(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__2() -> *mut LeanObject {
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = lean_unsigned_to_nat(11);
    v___x_1496_ = lean_nat_to_int(v___x_1495_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__3() -> *mut LeanObject {
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    v___x_1497_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__2_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__2,
    );
    v___x_1498_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1499_ = lean_int_add(v___x_1498_, v___x_1497_);
    return v___x_1499_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__4() -> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    v___x_1500_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1501_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__3,
    );
    v___x_1502_ = lean_int_sub(v___x_1501_, v___x_1500_);
    return v___x_1502_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5() -> *mut LeanObject {
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1505_: *mut LeanObject = core::ptr::null_mut();
    v___x_1503_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1504_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__4,
    );
    v_range_1505_ = lean_int_add(v___x_1504_, v___x_1503_);
    return v_range_1505_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6() -> *mut LeanObject {
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    v___x_1506_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1507_ = lean_int_sub(v___x_1506_, v___x_1506_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__7() -> *mut LeanObject {
    let mut v_range_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    v_range_1508_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5,
    );
    v___x_1509_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6,
    );
    v___x_1510_ = lean_int_emod(v___x_1509_, v_range_1508_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__8() -> *mut LeanObject {
    let mut v_range_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v_range_1511_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5,
    );
    v___x_1512_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__7_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__7,
    );
    v___x_1513_ = lean_int_add(v___x_1512_, v_range_1511_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__9() -> *mut LeanObject {
    let mut v_range_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v_range_1514_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5,
    );
    v___x_1515_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__8_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__8,
    );
    v___x_1516_ = lean_int_emod(v___x_1515_, v_range_1514_);
    return v___x_1516_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__10() -> *mut LeanObject
{
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    v___x_1517_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1518_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__9,
    );
    v___x_1519_ = lean_int_add(v___x_1518_, v___x_1517_);
    return v___x_1519_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11() -> *mut LeanObject
{
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    v___x_1520_ = lean_unsigned_to_nat(30);
    v___x_1521_ = lean_nat_to_int(v___x_1520_);
    return v___x_1521_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__12() -> *mut LeanObject
{
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    v___x_1522_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1523_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1524_ = lean_int_add(v___x_1523_, v___x_1522_);
    return v___x_1524_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__13() -> *mut LeanObject
{
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    v___x_1525_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1526_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__12_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__12,
    );
    v___x_1527_ = lean_int_sub(v___x_1526_, v___x_1525_);
    return v___x_1527_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14() -> *mut LeanObject
{
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1529_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__13,
    );
    v_range_1530_ = lean_int_add(v___x_1529_, v___x_1528_);
    return v_range_1530_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__15() -> *mut LeanObject
{
    let mut v_range_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    v_range_1531_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14,
    );
    v___x_1532_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6,
    );
    v___x_1533_ = lean_int_emod(v___x_1532_, v_range_1531_);
    return v___x_1533_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__16() -> *mut LeanObject
{
    let mut v_range_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    v_range_1534_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14,
    );
    v___x_1535_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__15_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__15,
    );
    v___x_1536_ = lean_int_add(v___x_1535_, v_range_1534_);
    return v___x_1536_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__17() -> *mut LeanObject
{
    let mut v_range_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    v_range_1537_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14,
    );
    v___x_1538_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__16_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__16,
    );
    v___x_1539_ = lean_int_emod(v___x_1538_, v_range_1537_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__18() -> *mut LeanObject
{
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    v___x_1540_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1541_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__17,
    );
    v___x_1542_ = lean_int_add(v___x_1541_, v___x_1540_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__19() -> *mut LeanObject
{
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1543_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__18,
    );
    v___x_1544_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__10_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__10,
    );
    v___x_1545_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1546_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1546_, 0, v___x_1545_);
    lean_ctor_set(v___x_1546_, 1, v___x_1544_);
    lean_ctor_set(v___x_1546_, 2, v___x_1543_);
    return v___x_1546_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__20() -> *mut LeanObject
{
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    v___x_1547_ = lean_unsigned_to_nat(23);
    v___x_1548_ = lean_nat_to_int(v___x_1547_);
    return v___x_1548_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__21() -> *mut LeanObject
{
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1549_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__20_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__20,
    );
    v___x_1550_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1551_ = lean_int_add(v___x_1550_, v___x_1549_);
    return v___x_1551_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__22() -> *mut LeanObject
{
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    v___x_1552_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1553_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__21_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__21,
    );
    v___x_1554_ = lean_int_sub(v___x_1553_, v___x_1552_);
    return v___x_1554_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23() -> *mut LeanObject
{
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1556_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__22_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__22,
    );
    v_range_1557_ = lean_int_add(v___x_1556_, v___x_1555_);
    return v_range_1557_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24() -> *mut LeanObject
{
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    v___x_1558_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1559_ = lean_int_sub(v___x_1558_, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__25() -> *mut LeanObject
{
    let mut v_range_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    v_range_1560_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23,
    );
    v___x_1561_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24,
    );
    v___x_1562_ = lean_int_emod(v___x_1561_, v_range_1560_);
    return v___x_1562_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__26() -> *mut LeanObject
{
    let mut v_range_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    v_range_1563_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23,
    );
    v___x_1564_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__25_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__25,
    );
    v___x_1565_ = lean_int_add(v___x_1564_, v_range_1563_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__27() -> *mut LeanObject
{
    let mut v_range_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    v_range_1566_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23,
    );
    v___x_1567_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__26_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__26,
    );
    v___x_1568_ = lean_int_emod(v___x_1567_, v_range_1566_);
    return v___x_1568_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__28() -> *mut LeanObject
{
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    v___x_1569_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1570_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__27),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__27_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__27,
    );
    v___x_1571_ = lean_int_add(v___x_1570_, v___x_1569_);
    return v___x_1571_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__29() -> *mut LeanObject
{
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    v___x_1572_ = lean_unsigned_to_nat(59);
    v___x_1573_ = lean_nat_to_int(v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__30() -> *mut LeanObject
{
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1574_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__29),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__29_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__29,
    );
    v___x_1575_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1576_ = lean_int_add(v___x_1575_, v___x_1574_);
    return v___x_1576_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__31() -> *mut LeanObject
{
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    v___x_1577_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1578_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__30),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__30_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__30,
    );
    v___x_1579_ = lean_int_sub(v___x_1578_, v___x_1577_);
    return v___x_1579_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32() -> *mut LeanObject
{
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1582_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__31),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__31_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__31,
    );
    v_range_1582_ = lean_int_add(v___x_1581_, v___x_1580_);
    return v_range_1582_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__33() -> *mut LeanObject
{
    let mut v_range_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    v_range_1583_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32,
    );
    v___x_1584_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24,
    );
    v___x_1585_ = lean_int_emod(v___x_1584_, v_range_1583_);
    return v___x_1585_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__34() -> *mut LeanObject
{
    let mut v_range_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    v_range_1586_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32,
    );
    v___x_1587_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__33),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__33_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__33,
    );
    v___x_1588_ = lean_int_add(v___x_1587_, v_range_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__35() -> *mut LeanObject
{
    let mut v_range_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    v_range_1589_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32,
    );
    v___x_1590_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__34),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__34_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__34,
    );
    v___x_1591_ = lean_int_emod(v___x_1590_, v_range_1589_);
    return v___x_1591_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__36() -> *mut LeanObject
{
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1592_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1593_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__35),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__35_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__35,
    );
    v___x_1594_ = lean_int_add(v___x_1593_, v___x_1592_);
    return v___x_1594_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__37() -> *mut LeanObject
{
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1595_ = lean_unsigned_to_nat(0);
    v___x_1596_ = 1;
    v___x_1597_ = l_Std_Time_Second_instOfNatOrdinal(v___x_1596_, v___x_1595_);
    return v___x_1597_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__38() -> *mut LeanObject
{
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1598_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1599_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__37),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__37_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__37,
    );
    v___x_1600_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__36),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__36_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__36,
    );
    v___x_1601_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__28),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__28_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__28,
    );
    v___x_1602_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1602_, 0, v___x_1601_);
    lean_ctor_set(v___x_1602_, 1, v___x_1600_);
    lean_ctor_set(v___x_1602_, 2, v___x_1599_);
    lean_ctor_set(v___x_1602_, 3, v___x_1598_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__39() -> *mut LeanObject
{
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    v___x_1603_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__38),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__38_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__38,
    );
    v___x_1604_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__19_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__19,
    );
    v___x_1605_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1605_, 0, v___x_1604_);
    lean_ctor_set(v___x_1605_, 1, v___x_1603_);
    return v___x_1605_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default() -> *mut LeanObject {
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v___x_1606_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__39),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__39_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__39,
    );
    return v___x_1606_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime() -> *mut LeanObject {
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    v___x_1607_ = l_Std_Time_instInhabitedPlainDateTime_default;
    return v___x_1607_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDateTime_decEq(
    mut v_x_1608_: *mut LeanObject,
    mut v_x_1609_: *mut LeanObject,
) -> u8 {
    let mut v_date_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    v_date_1610_ = lean_ctor_get(v_x_1608_, 0);
    v_time_1611_ = lean_ctor_get(v_x_1608_, 1);
    v_date_1612_ = lean_ctor_get(v_x_1609_, 0);
    v_time_1613_ = lean_ctor_get(v_x_1609_, 1);
    v___x_1614_ = l_Std_Time_instDecidableEqPlainDate_decEq(v_date_1610_, v_date_1612_);
    if v___x_1614_ == 0 {
        return v___x_1614_;
    } else {
        let mut v___x_1615_: u8 = 0;
        v___x_1615_ = l_Std_Time_instDecidableEqPlainTime_decEq(v_time_1611_, v_time_1613_);
        return v___x_1615_;
    }
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDateTime_decEq___boxed(
    mut v_x_1616_: *mut LeanObject,
    mut v_x_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1618_: u8 = 0;
    let mut v_r_1619_: *mut LeanObject = core::ptr::null_mut();
    v_res_1618_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_1616_, v_x_1617_);
    lean_dec_ref(v_x_1617_);
    lean_dec_ref(v_x_1616_);
    v_r_1619_ = lean_box((v_res_1618_) as usize);
    return v_r_1619_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDateTime(
    mut v_x_1620_: *mut LeanObject,
    mut v_x_1621_: *mut LeanObject,
) -> u8 {
    let mut v___x_1622_: u8 = 0;
    v___x_1622_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_1620_, v_x_1621_);
    return v___x_1622_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDateTime___boxed(
    mut v_x_1623_: *mut LeanObject,
    mut v_x_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1625_: u8 = 0;
    let mut v_r_1626_: *mut LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Std_Time_instDecidableEqPlainDateTime(v_x_1623_, v_x_1624_);
    lean_dec_ref(v_x_1624_);
    lean_dec_ref(v_x_1623_);
    v_r_1626_ = lean_box((v_res_1625_) as usize);
    return v_r_1626_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7() -> *mut LeanObject
{
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    v___x_1640_ = lean_unsigned_to_nat(8);
    v___x_1641_ = lean_nat_to_int(v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13() -> *mut LeanObject
{
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    v___x_1649_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0;
    v___x_1650_ = lean_string_length(v___x_1649_);
    return v___x_1650_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14() -> *mut LeanObject
{
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13_once),
        _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13,
    );
    v___x_1652_ = lean_nat_to_int(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Std_Time_instReprPlainDateTime_repr___redArg(
    mut v_x_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_1658_ = lean_ctor_get(v_x_1657_, 0);
                v_time_1659_ = lean_ctor_get(v_x_1657_, 1);
                v_isSharedCheck_1691_ = (!lean_is_exclusive(v_x_1657_)) as u8;
                if v_isSharedCheck_1691_ == 0 {
                    v___x_1661_ = v_x_1657_;
                    v_isShared_1662_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_1659_);
                    lean_inc(v_date_1658_);
                    lean_dec(v_x_1657_);
                    v___x_1661_ = lean_box(0);
                    v_isShared_1662_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1663_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5;
                v___x_1664_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6;
                v___x_1665_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7,
                );
                v___x_1666_ = l_Std_Time_instReprPlainDate_repr___redArg(v_date_1658_);
                lean_dec_ref(v_date_1658_);
                if v_isShared_1662_ == 0 {
                    lean_ctor_set_tag(v___x_1661_, 4);
                    lean_ctor_set(v___x_1661_, 1, v___x_1666_);
                    lean_ctor_set(v___x_1661_, 0, v___x_1665_);
                    v___x_1668_ = v___x_1661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = lean_alloc_ctor(4, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1665_);
                    lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1666_);
                    v___x_1668_ = v_reuseFailAlloc_1690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1669_ = 0;
                v___x_1670_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1670_, 0, v___x_1668_);
                lean_ctor_set_uint8(
                    v___x_1670_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1669_,
                );
                v___x_1671_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1671_, 0, v___x_1664_);
                lean_ctor_set(v___x_1671_, 1, v___x_1670_);
                v___x_1672_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9;
                v___x_1673_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1673_, 0, v___x_1671_);
                lean_ctor_set(v___x_1673_, 1, v___x_1672_);
                v___x_1674_ = lean_box(1);
                v___x_1675_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1675_, 0, v___x_1673_);
                lean_ctor_set(v___x_1675_, 1, v___x_1674_);
                v___x_1676_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11;
                v___x_1677_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1677_, 0, v___x_1675_);
                lean_ctor_set(v___x_1677_, 1, v___x_1676_);
                v___x_1678_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                lean_ctor_set(v___x_1678_, 1, v___x_1663_);
                v___x_1679_ = l_Std_Time_instReprPlainTime_repr___redArg(v_time_1659_);
                lean_dec_ref(v_time_1659_);
                v___x_1680_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1680_, 0, v___x_1665_);
                lean_ctor_set(v___x_1680_, 1, v___x_1679_);
                v___x_1681_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1681_, 0, v___x_1680_);
                lean_ctor_set_uint8(
                    v___x_1681_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1669_,
                );
                v___x_1682_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1682_, 0, v___x_1678_);
                lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                v___x_1683_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14,
                );
                v___x_1684_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15;
                v___x_1685_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1685_, 0, v___x_1684_);
                lean_ctor_set(v___x_1685_, 1, v___x_1682_);
                v___x_1686_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16;
                v___x_1687_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1687_, 0, v___x_1685_);
                lean_ctor_set(v___x_1687_, 1, v___x_1686_);
                v___x_1688_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1688_, 0, v___x_1683_);
                lean_ctor_set(v___x_1688_, 1, v___x_1687_);
                v___x_1689_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1689_, 0, v___x_1688_);
                lean_ctor_set_uint8(
                    v___x_1689_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1669_,
                );
                return v___x_1689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprPlainDateTime_repr(
    mut v_x_1692_: *mut LeanObject,
    mut v_prec_1693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_Std_Time_instReprPlainDateTime_repr___redArg(v_x_1692_);
    return v___x_1694_;
}
pub unsafe fn l_Std_Time_instReprPlainDateTime_repr___boxed(
    mut v_x_1695_: *mut LeanObject,
    mut v_prec_1696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1697_: *mut LeanObject = core::ptr::null_mut();
    v_res_1697_ = l_Std_Time_instReprPlainDateTime_repr(v_x_1695_, v_prec_1696_);
    lean_dec(v_prec_1696_);
    return v_res_1697_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__0(
    mut v_x_1700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_1701_: *mut LeanObject = core::ptr::null_mut();
    v_date_1701_ = lean_ctor_get(v_x_1700_, 0);
    lean_inc_ref(v_date_1701_);
    return v_date_1701_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__0___boxed(
    mut v_x_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Std_Time_instOrdPlainDateTime___lam__0(v_x_1702_);
    lean_dec_ref(v_x_1702_);
    return v_res_1703_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__1(
    mut v_x_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_1705_: *mut LeanObject = core::ptr::null_mut();
    v_time_1705_ = lean_ctor_get(v_x_1704_, 1);
    lean_inc_ref(v_time_1705_);
    return v_time_1705_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__1___boxed(
    mut v_x_1706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1707_: *mut LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Std_Time_instOrdPlainDateTime___lam__1(v_x_1706_);
    lean_dec_ref(v_x_1706_);
    return v_res_1707_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime___closed__2() -> *mut LeanObject {
    let mut v___f_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    v___f_1710_ = l_Std_Time_instOrdPlainDateTime___closed__0;
    v___x_1711_ = l_Std_Time_instOrdPlainDate;
    v___x_1712_ = lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_1712_, 0, lean_box(0));
    lean_closure_set(v___x_1712_, 1, lean_box(0));
    lean_closure_set(v___x_1712_, 2, v___x_1711_);
    lean_closure_set(v___x_1712_, 3, v___f_1710_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime___closed__3() -> *mut LeanObject {
    let mut v___f_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___f_1713_ = l_Std_Time_instOrdPlainDateTime___closed__1;
    v___x_1714_ = l_Std_Time_instOrdPlainTime;
    v___x_1715_ = lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_1715_, 0, lean_box(0));
    lean_closure_set(v___x_1715_, 1, lean_box(0));
    lean_closure_set(v___x_1715_, 2, v___x_1714_);
    lean_closure_set(v___x_1715_, 3, v___f_1713_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime___closed__4() -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__3_once),
        _init_l_Std_Time_instOrdPlainDateTime___closed__3,
    );
    v___x_1717_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__2_once),
        _init_l_Std_Time_instOrdPlainDateTime___closed__2,
    );
    v___x_1718_ = lean_alloc_closure(l_compareLex___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_1718_, 0, lean_box(0));
    lean_closure_set(v___x_1718_, 1, lean_box(0));
    lean_closure_set(v___x_1718_, 2, v___x_1717_);
    lean_closure_set(v___x_1718_, 3, v___x_1716_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime() -> *mut LeanObject {
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1719_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__4_once),
        _init_l_Std_Time_instOrdPlainDateTime___closed__4,
    );
    return v___x_1719_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__1(
    mut v_a_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Rat_ofInt(v_a_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_toWallTime___closed__0() -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = lean_unsigned_to_nat(86400);
    v___x_1723_ = lean_nat_to_int(v___x_1722_);
    return v___x_1723_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_toWallTime___closed__1() -> *mut LeanObject {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1724_ = lean_unsigned_to_nat(1000000000);
    v___x_1725_ = lean_nat_to_int(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toWallTime(
    mut v_dt_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_days_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanos_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    v_time_1727_ = lean_ctor_get(v_dt_1726_, 1);
    lean_inc_ref(v_time_1727_);
    v_date_1728_ = lean_ctor_get(v_dt_1726_, 0);
    lean_inc_ref(v_date_1728_);
    lean_dec_ref(v_dt_1726_);
    v_nanosecond_1729_ = lean_ctor_get(v_time_1727_, 3);
    lean_inc(v_nanosecond_1729_);
    v_days_1730_ = l_Std_Time_PlainDate_toEpochDay(v_date_1728_);
    v___x_1731_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__0,
    );
    v___x_1732_ = lean_int_mul(v_days_1730_, v___x_1731_);
    lean_dec(v_days_1730_);
    v___x_1733_ = l_Std_Time_PlainTime_toSeconds(v_time_1727_);
    lean_dec_ref(v_time_1727_);
    v___x_1734_ = lean_int_add(v___x_1732_, v___x_1733_);
    lean_dec(v___x_1733_);
    lean_dec(v___x_1732_);
    v___x_1735_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_1736_ = lean_int_mul(v___x_1734_, v___x_1735_);
    lean_dec(v___x_1734_);
    v_nanos_1737_ = lean_int_add(v___x_1736_, v_nanosecond_1729_);
    lean_dec(v_nanosecond_1729_);
    lean_dec(v___x_1736_);
    v___x_1738_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1737_);
    lean_dec(v_nanos_1737_);
    return v___x_1738_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__0(
    mut v_a_1739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v___x_1740_ = lean_nat_to_int(v_a_1739_);
    v___x_1741_ = l_Rat_ofInt(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    v___x_1742_ = lean_unsigned_to_nat(13);
    v___x_1743_ = lean_unsigned_to_nat(1);
    v___x_1744_ = lean_nat_mod(v___x_1743_, v___x_1742_);
    return v___x_1744_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(
    mut v_as_x27_1745_: *mut LeanObject,
    mut v_b_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_1745_) == 0 {
                    return v_b_1746_;
                } else {
                    v_head_1747_ = lean_ctor_get(v_as_x27_1745_, 0);
                    v_tail_1748_ = lean_ctor_get(v_as_x27_1745_, 1);
                    v_fst_1749_ = lean_ctor_get(v_b_1746_, 0);
                    v_snd_1750_ = lean_ctor_get(v_b_1746_, 1);
                    v_isSharedCheck_1766_ = (!lean_is_exclusive(v_b_1746_)) as u8;
                    if v_isSharedCheck_1766_ == 0 {
                        v___x_1752_ = v_b_1746_;
                        v_isShared_1753_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1750_);
                        lean_inc(v_fst_1749_);
                        lean_dec(v_b_1746_);
                        v___x_1752_ = lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1754_ = lean_unsigned_to_nat(13);
                v___x_1755_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0_once), _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0);
                v___x_1756_ = l_Fin_add(v___x_1754_, v_snd_1750_, v___x_1755_);
                lean_dec(v_snd_1750_);
                v___x_1757_ = lean_int_dec_lt(v_fst_1749_, v_head_1747_);
                if v___x_1757_ == 0 {
                    v___x_1758_ = lean_int_sub(v_fst_1749_, v_head_1747_);
                    lean_dec(v_fst_1749_);
                    if v_isShared_1753_ == 0 {
                        lean_ctor_set(v___x_1752_, 1, v___x_1756_);
                        lean_ctor_set(v___x_1752_, 0, v___x_1758_);
                        v___x_1760_ = v___x_1752_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1758_);
                        lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1756_);
                        v___x_1760_ = v_reuseFailAlloc_1762_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1753_ == 0 {
                        lean_ctor_set(v___x_1752_, 1, v___x_1756_);
                        v___x_1764_ = v___x_1752_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_fst_1749_);
                        lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1756_);
                        v___x_1764_ = v_reuseFailAlloc_1765_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_as_x27_1745_ = v_tail_1748_;
                v_b_1746_ = v___x_1760_;
                state = 0;
                continue;
            }
            3 => {
                return v___x_1764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___boxed(
    mut v_as_x27_1767_: *mut LeanObject,
    mut v_b_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1769_: *mut LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(
        v_as_x27_1767_,
        v_b_1768_,
    );
    lean_dec(v_as_x27_1767_);
    return v_res_1769_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0() -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_unsigned_to_nat(11017);
    v___x_1771_ = lean_nat_to_int(v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1() -> *mut LeanObject {
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    v___x_1772_ = lean_unsigned_to_nat(365);
    v___x_1773_ = lean_nat_to_int(v___x_1772_);
    return v___x_1773_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2() -> *mut LeanObject {
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    v___x_1774_ = lean_unsigned_to_nat(400);
    v___x_1775_ = lean_nat_to_int(v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3() -> *mut LeanObject {
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    v___x_1776_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
    );
    v___x_1777_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
    );
    v___x_1778_ = lean_int_mul(v___x_1777_, v___x_1776_);
    return v___x_1778_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4() -> *mut LeanObject {
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    v___x_1779_ = lean_unsigned_to_nat(97);
    v___x_1780_ = lean_nat_to_int(v___x_1779_);
    return v___x_1780_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5() -> *mut LeanObject {
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysPer400Y_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1781_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4,
    );
    v___x_1782_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__3_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3,
    );
    v_daysPer400Y_1783_ = lean_int_add(v___x_1782_, v___x_1781_);
    return v_daysPer400Y_1783_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6() -> *mut LeanObject {
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    v___x_1784_ = lean_unsigned_to_nat(100);
    v___x_1785_ = lean_nat_to_int(v___x_1784_);
    return v___x_1785_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7() -> *mut LeanObject {
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    v___x_1786_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
    );
    v___x_1787_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
    );
    v___x_1788_ = lean_int_mul(v___x_1787_, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8() -> *mut LeanObject {
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    v___x_1789_ = lean_unsigned_to_nat(24);
    v___x_1790_ = lean_nat_to_int(v___x_1789_);
    return v___x_1790_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9() -> *mut LeanObject {
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysPer100Y_1793_: *mut LeanObject = core::ptr::null_mut();
    v___x_1791_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__8_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8,
    );
    v___x_1792_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__7_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7,
    );
    v_daysPer100Y_1793_ = lean_int_add(v___x_1792_, v___x_1791_);
    return v_daysPer100Y_1793_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10() -> *mut LeanObject {
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    v___x_1794_ = lean_unsigned_to_nat(4);
    v___x_1795_ = lean_nat_to_int(v___x_1794_);
    return v___x_1795_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11() -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
    );
    v___x_1797_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
    );
    v___x_1798_ = lean_int_mul(v___x_1797_, v___x_1796_);
    return v___x_1798_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12() -> *mut LeanObject {
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysPer4Y_1801_: *mut LeanObject = core::ptr::null_mut();
    v___x_1799_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1800_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__11_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11,
    );
    v_daysPer4Y_1801_ = lean_int_add(v___x_1800_, v___x_1799_);
    return v_daysPer4Y_1801_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13() -> *mut LeanObject {
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    v___x_1802_ = lean_unsigned_to_nat(60);
    v___x_1803_ = lean_nat_to_int(v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14() -> *mut LeanObject {
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    v___x_1804_ = lean_unsigned_to_nat(3600);
    v___x_1805_ = lean_nat_to_int(v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15() -> *mut LeanObject {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    v___x_1806_ = lean_unsigned_to_nat(31);
    v___x_1807_ = lean_nat_to_int(v___x_1806_);
    return v___x_1807_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16() -> *mut LeanObject {
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    v___x_1808_ = lean_unsigned_to_nat(29);
    v___x_1809_ = lean_nat_to_int(v___x_1808_);
    return v___x_1809_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17() -> *mut LeanObject {
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    v___x_1810_ = lean_box(0);
    v___x_1811_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__16_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16,
    );
    v___x_1812_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    lean_ctor_set(v___x_1812_, 1, v___x_1810_);
    return v___x_1812_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18() -> *mut LeanObject {
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    v___x_1813_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__17_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17,
    );
    v___x_1814_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1815_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    lean_ctor_set(v___x_1815_, 1, v___x_1813_);
    return v___x_1815_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19() -> *mut LeanObject {
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    v___x_1816_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__18_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18,
    );
    v___x_1817_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1818_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1818_, 0, v___x_1817_);
    lean_ctor_set(v___x_1818_, 1, v___x_1816_);
    return v___x_1818_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20() -> *mut LeanObject {
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    v___x_1819_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__19_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19,
    );
    v___x_1820_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1821_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1821_, 0, v___x_1820_);
    lean_ctor_set(v___x_1821_, 1, v___x_1819_);
    return v___x_1821_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21() -> *mut LeanObject {
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    v___x_1822_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__20_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20,
    );
    v___x_1823_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1824_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1824_, 0, v___x_1823_);
    lean_ctor_set(v___x_1824_, 1, v___x_1822_);
    return v___x_1824_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22() -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__21_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21,
    );
    v___x_1826_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1827_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1827_, 0, v___x_1826_);
    lean_ctor_set(v___x_1827_, 1, v___x_1825_);
    return v___x_1827_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23() -> *mut LeanObject {
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    v___x_1828_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__22_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22,
    );
    v___x_1829_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1830_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1830_, 0, v___x_1829_);
    lean_ctor_set(v___x_1830_, 1, v___x_1828_);
    return v___x_1830_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24() -> *mut LeanObject {
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    v___x_1831_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__23_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23,
    );
    v___x_1832_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1833_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1833_, 0, v___x_1832_);
    lean_ctor_set(v___x_1833_, 1, v___x_1831_);
    return v___x_1833_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25() -> *mut LeanObject {
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    v___x_1834_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__24_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24,
    );
    v___x_1835_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1836_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1836_, 0, v___x_1835_);
    lean_ctor_set(v___x_1836_, 1, v___x_1834_);
    return v___x_1836_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26() -> *mut LeanObject {
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    v___x_1837_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__25_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25,
    );
    v___x_1838_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1839_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1839_, 0, v___x_1838_);
    lean_ctor_set(v___x_1839_, 1, v___x_1837_);
    return v___x_1839_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27() -> *mut LeanObject {
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    v___x_1840_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__26_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26,
    );
    v___x_1841_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1842_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1842_, 0, v___x_1841_);
    lean_ctor_set(v___x_1842_, 1, v___x_1840_);
    return v___x_1842_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28() -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_months_1845_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__27),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__27_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27,
    );
    v___x_1844_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v_months_1845_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v_months_1845_, 0, v___x_1844_);
    lean_ctor_set(v_months_1845_, 1, v___x_1843_);
    return v_months_1845_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29() -> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mon_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1846_ = lean_unsigned_to_nat(13);
    v___x_1847_ = lean_unsigned_to_nat(0);
    v_mon_1848_ = lean_nat_mod(v___x_1847_, v___x_1846_);
    return v_mon_1848_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30() -> *mut LeanObject {
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    v___x_1849_ = lean_unsigned_to_nat(2000);
    v___x_1850_ = lean_nat_to_int(v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31() -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ = lean_unsigned_to_nat(25);
    v___x_1852_ = lean_nat_to_int(v___x_1851_);
    return v___x_1852_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__32() -> *mut LeanObject {
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    v___x_1853_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1854_ = lean_int_neg(v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofWallTime(
    mut v_stamp_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1872_: u8 = 0;
    let mut v_max_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v_daysPer400Y_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysPer100Y_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: u8 = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysPer4Y_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hmon_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: u8 = 0;
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remYears_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remDays_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_months_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mon_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quadrennialCycles_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remDays_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remYears_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: u8 = 0;
    let mut v_remYears_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_centenialCycles_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remDays_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quadrennialCycles_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v_quadrennialCycles_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quadracentennialCycles_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remDays_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_centenialCycles_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: u8 = 0;
    let mut v_centenialCycles_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quadracentennialCycles_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remDays_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v_remDays_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quadracentennialCycles_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_boundedDaysSinceEpoch_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rawDays_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rawDays_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_secs_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_1877_ = lean_ctor_get(v_stamp_1855_, 0);
                v_nano_1878_ = lean_ctor_get(v_stamp_1855_, 1);
                v_isSharedCheck_2026_ = (!lean_is_exclusive(v_stamp_1855_)) as u8;
                if v_isSharedCheck_2026_ == 0 {
                    v___x_1880_ = v_stamp_1855_;
                    v_isShared_1881_ = v_isSharedCheck_2026_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nano_1878_);
                    lean_inc(v_second_1877_);
                    lean_dec(v_stamp_1855_);
                    v___x_1880_ = lean_box(0);
                    v_isShared_1881_ = v_isSharedCheck_2026_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1862_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_1862_, 0, v___y_1859_);
                lean_ctor_set(v___x_1862_, 1, v___y_1857_);
                lean_ctor_set(v___x_1862_, 2, v___y_1860_);
                lean_ctor_set(v___x_1862_, 3, v___y_1858_);
                v___x_1863_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1863_, 0, v___y_1861_);
                lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                return v___x_1863_;
            }
            2 => {
                v_max_1873_ = l_Std_Time_Month_Ordinal_days(v___y_1872_, v___y_1868_);
                v___x_1874_ = lean_int_dec_lt(v_max_1873_, v___y_1870_);
                if v___x_1874_ == 0 {
                    lean_dec(v_max_1873_);
                    v___x_1875_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1875_, 0, v___y_1869_);
                    lean_ctor_set(v___x_1875_, 1, v___y_1868_);
                    lean_ctor_set(v___x_1875_, 2, v___y_1870_);
                    v___y_1857_ = v___y_1865_;
                    v___y_1858_ = v___y_1867_;
                    v___y_1859_ = v___y_1866_;
                    v___y_1860_ = v___y_1871_;
                    v___y_1861_ = v___x_1875_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___y_1870_);
                    v___x_1876_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1876_, 0, v___y_1869_);
                    lean_ctor_set(v___x_1876_, 1, v___y_1868_);
                    lean_ctor_set(v___x_1876_, 2, v_max_1873_);
                    v___y_1857_ = v___y_1865_;
                    v___y_1858_ = v___y_1867_;
                    v___y_1859_ = v___y_1866_;
                    v___y_1860_ = v___y_1871_;
                    v___y_1861_ = v___x_1876_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1882_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0,
                );
                v___x_1883_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
                );
                v___x_1884_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v_daysPer400Y_1896_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__5_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5,
                );
                v___x_1897_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                );
                v_daysPer100Y_1898_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__9),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__9_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9,
                );
                v___x_1899_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_1914_ = lean_unsigned_to_nat(1);
                v___x_1915_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
                );
                v_daysPer4Y_1916_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__12),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__12_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12,
                );
                v___x_1917_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
                );
                v___x_1918_ = lean_int_mul(v_second_1877_, v___x_1917_);
                lean_dec(v_second_1877_);
                v___x_1919_ = lean_int_add(v___x_1918_, v_nano_1878_);
                lean_dec(v_nano_1878_);
                lean_dec(v___x_1918_);
                v_secs_2021_ = lean_int_div(v___x_1919_, v___x_1917_);
                v___x_2022_ = lean_int_mod(v___x_1919_, v___x_1917_);
                v___x_2023_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2024_ = lean_int_dec_lt(v___x_2022_, v___x_2023_);
                lean_dec(v___x_2022_);
                if v___x_2024_ == 0 {
                    v_snd_2012_ = v_secs_2021_;
                    state = 13;
                    continue;
                } else {
                    v___x_2025_ = lean_int_sub(v_secs_2021_, v___x_1915_);
                    lean_dec(v_secs_2021_);
                    v_snd_2012_ = v___x_2025_;
                    state = 13;
                    continue;
                }
            }
            4 => {
                v___x_1894_ = lean_int_mod(v___y_1891_, v___x_1884_);
                v___x_1895_ = lean_int_dec_eq(v___x_1894_, v___y_1887_);
                lean_dec(v___y_1887_);
                lean_dec(v___x_1894_);
                v___y_1865_ = v___y_1886_;
                v___y_1866_ = v___y_1890_;
                v___y_1867_ = v___y_1889_;
                v___y_1868_ = v___y_1888_;
                v___y_1869_ = v___y_1891_;
                v___y_1870_ = v___y_1892_;
                v___y_1871_ = v___y_1893_;
                v___y_1872_ = v___x_1895_;
                state = 2;
                continue;
            }
            5 => {
                v___x_1909_ = lean_int_mod(v___y_1906_, v___x_1899_);
                v___x_1910_ = lean_nat_to_int(v___y_1902_);
                v___x_1911_ = lean_int_dec_eq(v___x_1909_, v___x_1910_);
                lean_dec(v___x_1909_);
                if v___x_1911_ == 0 {
                    lean_dec(v___x_1910_);
                    v___y_1865_ = v___y_1901_;
                    v___y_1866_ = v___y_1905_;
                    v___y_1867_ = v___y_1904_;
                    v___y_1868_ = v___y_1903_;
                    v___y_1869_ = v___y_1906_;
                    v___y_1870_ = v___y_1908_;
                    v___y_1871_ = v___y_1907_;
                    v___y_1872_ = v___x_1911_;
                    state = 2;
                    continue;
                } else {
                    v___x_1912_ = lean_int_mod(v___y_1906_, v___x_1897_);
                    v___x_1913_ = lean_int_dec_eq(v___x_1912_, v___x_1910_);
                    lean_dec(v___x_1912_);
                    if v___x_1913_ == 0 {
                        if v___x_1911_ == 0 {
                            v___y_1886_ = v___y_1901_;
                            v___y_1887_ = v___x_1910_;
                            v___y_1888_ = v___y_1903_;
                            v___y_1889_ = v___y_1904_;
                            v___y_1890_ = v___y_1905_;
                            v___y_1891_ = v___y_1906_;
                            v___y_1892_ = v___y_1908_;
                            v___y_1893_ = v___y_1907_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___x_1910_);
                            v___y_1865_ = v___y_1901_;
                            v___y_1866_ = v___y_1905_;
                            v___y_1867_ = v___y_1904_;
                            v___y_1868_ = v___y_1903_;
                            v___y_1869_ = v___y_1906_;
                            v___y_1870_ = v___y_1908_;
                            v___y_1871_ = v___y_1907_;
                            v___y_1872_ = v___x_1911_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_1886_ = v___y_1901_;
                        v___y_1887_ = v___x_1910_;
                        v___y_1888_ = v___y_1903_;
                        v___y_1889_ = v___y_1904_;
                        v___y_1890_ = v___y_1905_;
                        v___y_1891_ = v___y_1906_;
                        v___y_1892_ = v___y_1908_;
                        v___y_1893_ = v___y_1907_;
                        state = 4;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1926_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__13),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__13_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13,
                );
                v___x_1927_ = lean_int_emod(v___y_1923_, v___x_1926_);
                v___x_1928_ = lean_int_ediv(v___y_1923_, v___x_1926_);
                v___x_1929_ = lean_int_emod(v___x_1928_, v___x_1926_);
                lean_dec(v___x_1928_);
                v___x_1930_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__14),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__14_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14,
                );
                v___x_1931_ = lean_int_ediv(v___y_1923_, v___x_1930_);
                lean_dec(v___y_1923_);
                v___x_1932_ = lean_int_emod(v___x_1919_, v___x_1917_);
                lean_dec(v___x_1919_);
                v___x_1933_ = l_Fin_succ___redArg(v___y_1921_);
                lean_dec(v___y_1921_);
                v___x_1934_ = lean_nat_dec_le(v___x_1914_, v___x_1933_);
                if v___x_1934_ == 0 {
                    lean_dec(v___x_1933_);
                    v___y_1901_ = v___x_1929_;
                    v___y_1902_ = v___y_1922_;
                    v___y_1903_ = v_hmon_1924_;
                    v___y_1904_ = v___x_1932_;
                    v___y_1905_ = v___x_1931_;
                    v___y_1906_ = v_year_1925_;
                    v___y_1907_ = v___x_1927_;
                    v___y_1908_ = v___x_1915_;
                    state = 5;
                    continue;
                } else {
                    v___x_1935_ = lean_nat_to_int(v___x_1933_);
                    v___y_1901_ = v___x_1929_;
                    v___y_1902_ = v___y_1922_;
                    v___y_1903_ = v_hmon_1924_;
                    v___y_1904_ = v___x_1932_;
                    v___y_1905_ = v___x_1931_;
                    v___y_1906_ = v_year_1925_;
                    v___y_1907_ = v___x_1927_;
                    v___y_1908_ = v___x_1935_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                v___x_1943_ = lean_int_mul(v_remYears_1942_, v___x_1883_);
                v_remDays_1944_ = lean_int_sub(v___y_1940_, v___x_1943_);
                lean_dec(v___x_1943_);
                lean_dec(v___y_1940_);
                v___x_1945_ = lean_unsigned_to_nat(31);
                v_months_1946_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__28),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__28_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28,
                );
                v___x_1947_ = lean_unsigned_to_nat(0);
                v_mon_1948_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__29),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__29_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29,
                );
                if v_isShared_1881_ == 0 {
                    lean_ctor_set(v___x_1880_, 1, v_mon_1948_);
                    lean_ctor_set(v___x_1880_, 0, v_remDays_1944_);
                    v___x_1950_ = v___x_1880_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_remDays_1944_);
                    lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_mon_1948_);
                    v___x_1950_ = v_reuseFailAlloc_1972_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1951_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_months_1946_, v___x_1950_);
                v_fst_1952_ = lean_ctor_get(v___x_1951_, 0);
                lean_inc(v_fst_1952_);
                v_snd_1953_ = lean_ctor_get(v___x_1951_, 1);
                lean_inc(v_snd_1953_);
                lean_dec_ref(v___x_1951_);
                v___x_1954_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__30),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__30_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30,
                );
                v___x_1955_ = lean_int_add(v___x_1954_, v_remYears_1942_);
                lean_dec(v_remYears_1942_);
                v___x_1956_ = lean_int_mul(v___x_1899_, v___y_1938_);
                lean_dec(v___y_1938_);
                v___x_1957_ = lean_int_add(v___x_1955_, v___x_1956_);
                lean_dec(v___x_1956_);
                lean_dec(v___x_1955_);
                v___x_1958_ = lean_int_mul(v___x_1897_, v___y_1937_);
                lean_dec(v___y_1937_);
                v___x_1959_ = lean_int_add(v___x_1957_, v___x_1958_);
                lean_dec(v___x_1958_);
                lean_dec(v___x_1957_);
                v___x_1960_ = lean_int_mul(v___x_1884_, v___y_1939_);
                lean_dec(v___y_1939_);
                v_year_1961_ = lean_int_add(v___x_1959_, v___x_1960_);
                lean_dec(v___x_1960_);
                lean_dec(v___x_1959_);
                v___x_1962_ = l_Int_toNat(v_fst_1952_);
                lean_dec(v_fst_1952_);
                v___x_1963_ = lean_nat_mod(v___x_1962_, v___x_1945_);
                lean_dec(v___x_1962_);
                v___x_1964_ = lean_unsigned_to_nat(10);
                v___x_1965_ = lean_nat_dec_lt(v___x_1964_, v_snd_1953_);
                if v___x_1965_ == 0 {
                    v___x_1966_ = lean_unsigned_to_nat(2);
                    v___x_1967_ = lean_nat_add(v_snd_1953_, v___x_1966_);
                    lean_dec(v_snd_1953_);
                    v___x_1968_ = lean_nat_to_int(v___x_1967_);
                    v___y_1921_ = v___x_1963_;
                    v___y_1922_ = v___x_1947_;
                    v___y_1923_ = v___y_1941_;
                    v_hmon_1924_ = v___x_1968_;
                    v_year_1925_ = v_year_1961_;
                    state = 6;
                    continue;
                } else {
                    v___x_1969_ = lean_int_add(v_year_1961_, v___x_1915_);
                    lean_dec(v_year_1961_);
                    v___x_1970_ = lean_nat_sub(v_snd_1953_, v___x_1964_);
                    lean_dec(v_snd_1953_);
                    v___x_1971_ = lean_nat_to_int(v___x_1970_);
                    v___y_1921_ = v___x_1963_;
                    v___y_1922_ = v___x_1947_;
                    v___y_1923_ = v___y_1941_;
                    v_hmon_1924_ = v___x_1971_;
                    v_year_1925_ = v___x_1969_;
                    state = 6;
                    continue;
                }
            }
            9 => {
                v___x_1979_ = lean_int_mul(v_quadrennialCycles_1978_, v_daysPer4Y_1916_);
                v_remDays_1980_ = lean_int_sub(v___y_1975_, v___x_1979_);
                lean_dec(v___x_1979_);
                lean_dec(v___y_1975_);
                v_remYears_1981_ = lean_int_ediv(v_remDays_1980_, v___x_1883_);
                v___x_1982_ = lean_int_dec_eq(v_remYears_1981_, v___x_1899_);
                if v___x_1982_ == 0 {
                    v___y_1937_ = v___y_1974_;
                    v___y_1938_ = v_quadrennialCycles_1978_;
                    v___y_1939_ = v___y_1976_;
                    v___y_1940_ = v_remDays_1980_;
                    v___y_1941_ = v___y_1977_;
                    v_remYears_1942_ = v_remYears_1981_;
                    state = 7;
                    continue;
                } else {
                    v_remYears_1983_ = lean_int_sub(v_remYears_1981_, v___x_1915_);
                    lean_dec(v_remYears_1981_);
                    v___y_1937_ = v___y_1974_;
                    v___y_1938_ = v_quadrennialCycles_1978_;
                    v___y_1939_ = v___y_1976_;
                    v___y_1940_ = v_remDays_1980_;
                    v___y_1941_ = v___y_1977_;
                    v_remYears_1942_ = v_remYears_1983_;
                    state = 7;
                    continue;
                }
            }
            10 => {
                v___x_1989_ = lean_int_mul(v_centenialCycles_1988_, v_daysPer100Y_1898_);
                v_remDays_1990_ = lean_int_sub(v___y_1986_, v___x_1989_);
                lean_dec(v___x_1989_);
                lean_dec(v___y_1986_);
                v_quadrennialCycles_1991_ = lean_int_ediv(v_remDays_1990_, v_daysPer4Y_1916_);
                v___x_1992_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__31),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__31_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31,
                );
                v___x_1993_ = lean_int_dec_eq(v_quadrennialCycles_1991_, v___x_1992_);
                if v___x_1993_ == 0 {
                    v___y_1974_ = v_centenialCycles_1988_;
                    v___y_1975_ = v_remDays_1990_;
                    v___y_1976_ = v___y_1985_;
                    v___y_1977_ = v___y_1987_;
                    v_quadrennialCycles_1978_ = v_quadrennialCycles_1991_;
                    state = 9;
                    continue;
                } else {
                    v_quadrennialCycles_1994_ =
                        lean_int_sub(v_quadrennialCycles_1991_, v___x_1915_);
                    lean_dec(v_quadrennialCycles_1991_);
                    v___y_1974_ = v_centenialCycles_1988_;
                    v___y_1975_ = v_remDays_1990_;
                    v___y_1976_ = v___y_1985_;
                    v___y_1977_ = v___y_1987_;
                    v_quadrennialCycles_1978_ = v_quadrennialCycles_1994_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_centenialCycles_1999_ = lean_int_ediv(v_remDays_1998_, v_daysPer100Y_1898_);
                v___x_2000_ = lean_int_dec_eq(v_centenialCycles_1999_, v___x_1899_);
                if v___x_2000_ == 0 {
                    v___y_1985_ = v_quadracentennialCycles_1997_;
                    v___y_1986_ = v_remDays_1998_;
                    v___y_1987_ = v___y_1996_;
                    v_centenialCycles_1988_ = v_centenialCycles_1999_;
                    state = 10;
                    continue;
                } else {
                    v_centenialCycles_2001_ = lean_int_sub(v_centenialCycles_1999_, v___x_1915_);
                    lean_dec(v_centenialCycles_1999_);
                    v___y_1985_ = v_quadracentennialCycles_1997_;
                    v___y_1986_ = v_remDays_1998_;
                    v___y_1987_ = v___y_1996_;
                    v_centenialCycles_1988_ = v_centenialCycles_2001_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                v_quadracentennialCycles_2005_ = lean_int_ediv(v_snd_2004_, v_daysPer400Y_1896_);
                v_remDays_2006_ = lean_int_emod(v_snd_2004_, v_daysPer400Y_1896_);
                lean_dec(v_snd_2004_);
                v___x_2007_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2008_ = lean_int_dec_lt(v_remDays_2006_, v___x_2007_);
                if v___x_2008_ == 0 {
                    v___y_1996_ = v_fst_2003_;
                    v_quadracentennialCycles_1997_ = v_quadracentennialCycles_2005_;
                    v_remDays_1998_ = v_remDays_2006_;
                    state = 11;
                    continue;
                } else {
                    v_remDays_2009_ = lean_int_add(v_remDays_2006_, v_daysPer400Y_1896_);
                    lean_dec(v_remDays_2006_);
                    v_quadracentennialCycles_2010_ =
                        lean_int_sub(v_quadracentennialCycles_2005_, v___x_1915_);
                    lean_dec(v_quadracentennialCycles_2005_);
                    v___y_1996_ = v_fst_2003_;
                    v_quadracentennialCycles_1997_ = v_quadracentennialCycles_2010_;
                    v_remDays_1998_ = v_remDays_2009_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_2013_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_toWallTime___closed__0,
                );
                v_boundedDaysSinceEpoch_2014_ = lean_int_div(v_snd_2012_, v___x_2013_);
                v_rawDays_2015_ = lean_int_sub(v_boundedDaysSinceEpoch_2014_, v___x_1882_);
                lean_dec(v_boundedDaysSinceEpoch_2014_);
                v_h_2016_ = lean_int_mod(v_snd_2012_, v___x_2013_);
                lean_dec(v_snd_2012_);
                v___x_2017_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__32),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__32_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__32,
                );
                v___x_2018_ = lean_int_dec_le(v_h_2016_, v___x_2017_);
                if v___x_2018_ == 0 {
                    v_fst_2003_ = v_h_2016_;
                    v_snd_2004_ = v_rawDays_2015_;
                    state = 12;
                    continue;
                } else {
                    v___x_2019_ = lean_int_add(v_h_2016_, v___x_2013_);
                    lean_dec(v_h_2016_);
                    v_rawDays_2020_ = lean_int_sub(v_rawDays_2015_, v___x_1915_);
                    lean_dec(v_rawDays_2015_);
                    v_fst_2003_ = v___x_2019_;
                    v_snd_2004_ = v_rawDays_2020_;
                    state = 12;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(
    mut v_as_2027_: *mut LeanObject,
    mut v_as_x27_2028_: *mut LeanObject,
    mut v_b_2029_: *mut LeanObject,
    mut v_a_2030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(
        v_as_x27_2028_,
        v_b_2029_,
    );
    return v___x_2031_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___boxed(
    mut v_as_2032_: *mut LeanObject,
    mut v_as_x27_2033_: *mut LeanObject,
    mut v_b_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2036_: *mut LeanObject = core::ptr::null_mut();
    v_res_2036_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(
        v_as_2032_,
        v_as_x27_2033_,
        v_b_2034_,
        v_a_2035_,
    );
    lean_dec(v_as_x27_2033_);
    lean_dec(v_as_2032_);
    return v_res_2036_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toEpochDay(
    mut v_pdt_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    v_date_2038_ = lean_ctor_get(v_pdt_2037_, 0);
    lean_inc_ref(v_date_2038_);
    lean_dec_ref(v_pdt_2037_);
    v___x_2039_ = l_Std_Time_PlainDate_toEpochDay(v_date_2038_);
    return v___x_2039_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofEpochDay(
    mut v_days_2040_: *mut LeanObject,
    mut v_time_2041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_Std_Time_PlainDate_ofEpochDay(v_days_2040_);
    v___x_2043_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2043_, 0, v___x_2042_);
    lean_ctor_set(v___x_2043_, 1, v_time_2041_);
    return v___x_2043_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofEpochDay___boxed(
    mut v_days_2044_: *mut LeanObject,
    mut v_time_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2046_: *mut LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Std_Time_PlainDateTime_ofEpochDay(v_days_2044_, v_time_2045_);
    lean_dec(v_days_2044_);
    return v_res_2046_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withWeekday(
    mut v_dt_2047_: *mut LeanObject,
    mut v_desiredWeekday_2048_: u8,
) -> *mut LeanObject {
    let mut v_date_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2049_ = lean_ctor_get(v_dt_2047_, 0);
                v_time_2050_ = lean_ctor_get(v_dt_2047_, 1);
                v_isSharedCheck_2058_ = (!lean_is_exclusive(v_dt_2047_)) as u8;
                if v_isSharedCheck_2058_ == 0 {
                    v___x_2052_ = v_dt_2047_;
                    v_isShared_2053_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2050_);
                    lean_inc(v_date_2049_);
                    lean_dec(v_dt_2047_);
                    v___x_2052_ = lean_box(0);
                    v_isShared_2053_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2054_ =
                    l_Std_Time_PlainDate_withWeekday(v_date_2049_, v_desiredWeekday_2048_);
                if v_isShared_2053_ == 0 {
                    lean_ctor_set(v___x_2052_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
                    lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_time_2050_);
                    v___x_2056_ = v_reuseFailAlloc_2057_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2056_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withWeekday___boxed(
    mut v_dt_2059_: *mut LeanObject,
    mut v_desiredWeekday_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_desiredWeekday_boxed_2061_: u8 = 0;
    let mut v_res_2062_: *mut LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_2061_ = (lean_unbox(v_desiredWeekday_2060_) as u8);
    v_res_2062_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_2059_, v_desiredWeekday_boxed_2061_);
    return v_res_2062_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withDaysClip(
    mut v_dt_2063_: *mut LeanObject,
    mut v_days_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v_year_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2074_: u8 = 0;
    let mut v___y_2076_: u8 = 0;
    let mut v_max_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_unused_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2065_ = lean_ctor_get(v_dt_2063_, 0);
                v_time_2066_ = lean_ctor_get(v_dt_2063_, 1);
                v_isSharedCheck_2104_ = (!lean_is_exclusive(v_dt_2063_)) as u8;
                if v_isSharedCheck_2104_ == 0 {
                    v___x_2068_ = v_dt_2063_;
                    v_isShared_2069_ = v_isSharedCheck_2104_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2066_);
                    lean_inc(v_date_2065_);
                    lean_dec(v_dt_2063_);
                    v___x_2068_ = lean_box(0);
                    v_isShared_2069_ = v_isSharedCheck_2104_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2070_ = lean_ctor_get(v_date_2065_, 0);
                v_month_2071_ = lean_ctor_get(v_date_2065_, 1);
                v_isSharedCheck_2102_ = (!lean_is_exclusive(v_date_2065_)) as u8;
                if v_isSharedCheck_2102_ == 0 {
                    v_unused_2103_ = lean_ctor_get(v_date_2065_, 2);
                    lean_dec(v_unused_2103_);
                    v___x_2073_ = v_date_2065_;
                    v_isShared_2074_ = v_isSharedCheck_2102_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_month_2071_);
                    lean_inc(v_year_2070_);
                    lean_dec(v_date_2065_);
                    v___x_2073_ = lean_box(0);
                    v_isShared_2074_ = v_isSharedCheck_2102_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2091_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2092_ = lean_int_mod(v_year_2070_, v___x_2091_);
                v___x_2093_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2098_ = lean_int_dec_eq(v___x_2092_, v___x_2093_);
                lean_dec(v___x_2092_);
                if v___x_2098_ == 0 {
                    v___y_2076_ = v___x_2098_;
                    state = 3;
                    continue;
                } else {
                    v___x_2099_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2100_ = lean_int_mod(v_year_2070_, v___x_2099_);
                    v___x_2101_ = lean_int_dec_eq(v___x_2100_, v___x_2093_);
                    lean_dec(v___x_2100_);
                    if v___x_2101_ == 0 {
                        if v___x_2098_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v___y_2076_ = v___x_2098_;
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_max_2077_ = l_Std_Time_Month_Ordinal_days(v___y_2076_, v_month_2071_);
                v___x_2078_ = lean_int_dec_lt(v_max_2077_, v_days_2064_);
                if v___x_2078_ == 0 {
                    lean_dec(v_max_2077_);
                    if v_isShared_2074_ == 0 {
                        lean_ctor_set(v___x_2073_, 2, v_days_2064_);
                        v___x_2080_ = v___x_2073_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_year_2070_);
                        lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_month_2071_);
                        lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_days_2064_);
                        v___x_2080_ = v_reuseFailAlloc_2084_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_days_2064_);
                    if v_isShared_2074_ == 0 {
                        lean_ctor_set(v___x_2073_, 2, v_max_2077_);
                        v___x_2086_ = v___x_2073_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_year_2070_);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_month_2071_);
                        lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_max_2077_);
                        v___x_2086_ = v_reuseFailAlloc_2090_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2069_ == 0 {
                    lean_ctor_set(v___x_2068_, 0, v___x_2080_);
                    v___x_2082_ = v___x_2068_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
                    lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_time_2066_);
                    v___x_2082_ = v_reuseFailAlloc_2083_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2082_;
            }
            6 => {
                if v_isShared_2069_ == 0 {
                    lean_ctor_set(v___x_2068_, 0, v___x_2086_);
                    v___x_2088_ = v___x_2068_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
                    lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_time_2066_);
                    v___x_2088_ = v_reuseFailAlloc_2089_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2088_;
            }
            8 => {
                v___x_2095_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2096_ = lean_int_mod(v_year_2070_, v___x_2095_);
                v___x_2097_ = lean_int_dec_eq(v___x_2096_, v___x_2093_);
                lean_dec(v___x_2096_);
                v___y_2076_ = v___x_2097_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withDaysRollOver(
    mut v_dt_2105_: *mut LeanObject,
    mut v_days_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v_year_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2107_ = lean_ctor_get(v_dt_2105_, 0);
                v_time_2108_ = lean_ctor_get(v_dt_2105_, 1);
                v_isSharedCheck_2118_ = (!lean_is_exclusive(v_dt_2105_)) as u8;
                if v_isSharedCheck_2118_ == 0 {
                    v___x_2110_ = v_dt_2105_;
                    v_isShared_2111_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2108_);
                    lean_inc(v_date_2107_);
                    lean_dec(v_dt_2105_);
                    v___x_2110_ = lean_box(0);
                    v_isShared_2111_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2112_ = lean_ctor_get(v_date_2107_, 0);
                lean_inc(v_year_2112_);
                v_month_2113_ = lean_ctor_get(v_date_2107_, 1);
                lean_inc(v_month_2113_);
                lean_dec_ref(v_date_2107_);
                v___x_2114_ =
                    l_Std_Time_PlainDate_rollOver(v_year_2112_, v_month_2113_, v_days_2106_);
                if v_isShared_2111_ == 0 {
                    lean_ctor_set(v___x_2110_, 0, v___x_2114_);
                    v___x_2116_ = v___x_2110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_time_2108_);
                    v___x_2116_ = v_reuseFailAlloc_2117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withDaysRollOver___boxed(
    mut v_dt_2119_: *mut LeanObject,
    mut v_days_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2121_: *mut LeanObject = core::ptr::null_mut();
    v_res_2121_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_2119_, v_days_2120_);
    lean_dec(v_days_2120_);
    return v_res_2121_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withMonthClip(
    mut v_dt_2122_: *mut LeanObject,
    mut v_month_2123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v_year_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___y_2135_: u8 = 0;
    let mut v_max_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: u8 = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_unused_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2124_ = lean_ctor_get(v_dt_2122_, 0);
                v_time_2125_ = lean_ctor_get(v_dt_2122_, 1);
                v_isSharedCheck_2163_ = (!lean_is_exclusive(v_dt_2122_)) as u8;
                if v_isSharedCheck_2163_ == 0 {
                    v___x_2127_ = v_dt_2122_;
                    v_isShared_2128_ = v_isSharedCheck_2163_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2125_);
                    lean_inc(v_date_2124_);
                    lean_dec(v_dt_2122_);
                    v___x_2127_ = lean_box(0);
                    v_isShared_2128_ = v_isSharedCheck_2163_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2129_ = lean_ctor_get(v_date_2124_, 0);
                v_day_2130_ = lean_ctor_get(v_date_2124_, 2);
                v_isSharedCheck_2161_ = (!lean_is_exclusive(v_date_2124_)) as u8;
                if v_isSharedCheck_2161_ == 0 {
                    v_unused_2162_ = lean_ctor_get(v_date_2124_, 1);
                    lean_dec(v_unused_2162_);
                    v___x_2132_ = v_date_2124_;
                    v_isShared_2133_ = v_isSharedCheck_2161_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_day_2130_);
                    lean_inc(v_year_2129_);
                    lean_dec(v_date_2124_);
                    v___x_2132_ = lean_box(0);
                    v_isShared_2133_ = v_isSharedCheck_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2150_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2151_ = lean_int_mod(v_year_2129_, v___x_2150_);
                v___x_2152_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2157_ = lean_int_dec_eq(v___x_2151_, v___x_2152_);
                lean_dec(v___x_2151_);
                if v___x_2157_ == 0 {
                    v___y_2135_ = v___x_2157_;
                    state = 3;
                    continue;
                } else {
                    v___x_2158_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2159_ = lean_int_mod(v_year_2129_, v___x_2158_);
                    v___x_2160_ = lean_int_dec_eq(v___x_2159_, v___x_2152_);
                    lean_dec(v___x_2159_);
                    if v___x_2160_ == 0 {
                        if v___x_2157_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v___y_2135_ = v___x_2157_;
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_max_2136_ = l_Std_Time_Month_Ordinal_days(v___y_2135_, v_month_2123_);
                v___x_2137_ = lean_int_dec_lt(v_max_2136_, v_day_2130_);
                if v___x_2137_ == 0 {
                    lean_dec(v_max_2136_);
                    if v_isShared_2133_ == 0 {
                        lean_ctor_set(v___x_2132_, 1, v_month_2123_);
                        v___x_2139_ = v___x_2132_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2143_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_year_2129_);
                        lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_month_2123_);
                        lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_day_2130_);
                        v___x_2139_ = v_reuseFailAlloc_2143_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_day_2130_);
                    if v_isShared_2133_ == 0 {
                        lean_ctor_set(v___x_2132_, 2, v_max_2136_);
                        lean_ctor_set(v___x_2132_, 1, v_month_2123_);
                        v___x_2145_ = v___x_2132_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_year_2129_);
                        lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_month_2123_);
                        lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_max_2136_);
                        v___x_2145_ = v_reuseFailAlloc_2149_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2128_ == 0 {
                    lean_ctor_set(v___x_2127_, 0, v___x_2139_);
                    v___x_2141_ = v___x_2127_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
                    lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_time_2125_);
                    v___x_2141_ = v_reuseFailAlloc_2142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2141_;
            }
            6 => {
                if v_isShared_2128_ == 0 {
                    lean_ctor_set(v___x_2127_, 0, v___x_2145_);
                    v___x_2147_ = v___x_2127_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
                    lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_time_2125_);
                    v___x_2147_ = v_reuseFailAlloc_2148_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2147_;
            }
            8 => {
                v___x_2154_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2155_ = lean_int_mod(v_year_2129_, v___x_2154_);
                v___x_2156_ = lean_int_dec_eq(v___x_2155_, v___x_2152_);
                lean_dec(v___x_2155_);
                v___y_2135_ = v___x_2156_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withMonthRollOver(
    mut v_dt_2164_: *mut LeanObject,
    mut v_month_2165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v_year_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2166_ = lean_ctor_get(v_dt_2164_, 0);
                v_time_2167_ = lean_ctor_get(v_dt_2164_, 1);
                v_isSharedCheck_2177_ = (!lean_is_exclusive(v_dt_2164_)) as u8;
                if v_isSharedCheck_2177_ == 0 {
                    v___x_2169_ = v_dt_2164_;
                    v_isShared_2170_ = v_isSharedCheck_2177_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2167_);
                    lean_inc(v_date_2166_);
                    lean_dec(v_dt_2164_);
                    v___x_2169_ = lean_box(0);
                    v_isShared_2170_ = v_isSharedCheck_2177_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2171_ = lean_ctor_get(v_date_2166_, 0);
                lean_inc(v_year_2171_);
                v_day_2172_ = lean_ctor_get(v_date_2166_, 2);
                lean_inc(v_day_2172_);
                lean_dec_ref(v_date_2166_);
                v___x_2173_ =
                    l_Std_Time_PlainDate_rollOver(v_year_2171_, v_month_2165_, v_day_2172_);
                lean_dec(v_day_2172_);
                if v_isShared_2170_ == 0 {
                    lean_ctor_set(v___x_2169_, 0, v___x_2173_);
                    v___x_2175_ = v___x_2169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
                    lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_time_2167_);
                    v___x_2175_ = v_reuseFailAlloc_2176_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withYearClip(
    mut v_dt_2178_: *mut LeanObject,
    mut v_year_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v_month_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___y_2191_: u8 = 0;
    let mut v_max_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_unused_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2180_ = lean_ctor_get(v_dt_2178_, 0);
                v_time_2181_ = lean_ctor_get(v_dt_2178_, 1);
                v_isSharedCheck_2219_ = (!lean_is_exclusive(v_dt_2178_)) as u8;
                if v_isSharedCheck_2219_ == 0 {
                    v___x_2183_ = v_dt_2178_;
                    v_isShared_2184_ = v_isSharedCheck_2219_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2181_);
                    lean_inc(v_date_2180_);
                    lean_dec(v_dt_2178_);
                    v___x_2183_ = lean_box(0);
                    v_isShared_2184_ = v_isSharedCheck_2219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_month_2185_ = lean_ctor_get(v_date_2180_, 1);
                v_day_2186_ = lean_ctor_get(v_date_2180_, 2);
                v_isSharedCheck_2217_ = (!lean_is_exclusive(v_date_2180_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v_unused_2218_ = lean_ctor_get(v_date_2180_, 0);
                    lean_dec(v_unused_2218_);
                    v___x_2188_ = v_date_2180_;
                    v_isShared_2189_ = v_isSharedCheck_2217_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_day_2186_);
                    lean_inc(v_month_2185_);
                    lean_dec(v_date_2180_);
                    v___x_2188_ = lean_box(0);
                    v_isShared_2189_ = v_isSharedCheck_2217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2206_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2207_ = lean_int_mod(v_year_2179_, v___x_2206_);
                v___x_2208_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2213_ = lean_int_dec_eq(v___x_2207_, v___x_2208_);
                lean_dec(v___x_2207_);
                if v___x_2213_ == 0 {
                    v___y_2191_ = v___x_2213_;
                    state = 3;
                    continue;
                } else {
                    v___x_2214_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2215_ = lean_int_mod(v_year_2179_, v___x_2214_);
                    v___x_2216_ = lean_int_dec_eq(v___x_2215_, v___x_2208_);
                    lean_dec(v___x_2215_);
                    if v___x_2216_ == 0 {
                        if v___x_2213_ == 0 {
                            state = 8;
                            continue;
                        } else {
                            v___y_2191_ = v___x_2213_;
                            state = 3;
                            continue;
                        }
                    } else {
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_max_2192_ = l_Std_Time_Month_Ordinal_days(v___y_2191_, v_month_2185_);
                v___x_2193_ = lean_int_dec_lt(v_max_2192_, v_day_2186_);
                if v___x_2193_ == 0 {
                    lean_dec(v_max_2192_);
                    if v_isShared_2189_ == 0 {
                        lean_ctor_set(v___x_2188_, 0, v_year_2179_);
                        v___x_2195_ = v___x_2188_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_year_2179_);
                        lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_month_2185_);
                        lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_day_2186_);
                        v___x_2195_ = v_reuseFailAlloc_2199_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_day_2186_);
                    if v_isShared_2189_ == 0 {
                        lean_ctor_set(v___x_2188_, 2, v_max_2192_);
                        lean_ctor_set(v___x_2188_, 0, v_year_2179_);
                        v___x_2201_ = v___x_2188_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_year_2179_);
                        lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_month_2185_);
                        lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_max_2192_);
                        v___x_2201_ = v_reuseFailAlloc_2205_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2184_ == 0 {
                    lean_ctor_set(v___x_2183_, 0, v___x_2195_);
                    v___x_2197_ = v___x_2183_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
                    lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_time_2181_);
                    v___x_2197_ = v_reuseFailAlloc_2198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2197_;
            }
            6 => {
                if v_isShared_2184_ == 0 {
                    lean_ctor_set(v___x_2183_, 0, v___x_2201_);
                    v___x_2203_ = v___x_2183_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
                    lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_time_2181_);
                    v___x_2203_ = v_reuseFailAlloc_2204_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2203_;
            }
            8 => {
                v___x_2210_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2211_ = lean_int_mod(v_year_2179_, v___x_2210_);
                v___x_2212_ = lean_int_dec_eq(v___x_2211_, v___x_2208_);
                lean_dec(v___x_2211_);
                v___y_2191_ = v___x_2212_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withYearRollOver(
    mut v_dt_2220_: *mut LeanObject,
    mut v_year_2221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v_month_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2222_ = lean_ctor_get(v_dt_2220_, 0);
                v_time_2223_ = lean_ctor_get(v_dt_2220_, 1);
                v_isSharedCheck_2233_ = (!lean_is_exclusive(v_dt_2220_)) as u8;
                if v_isSharedCheck_2233_ == 0 {
                    v___x_2225_ = v_dt_2220_;
                    v_isShared_2226_ = v_isSharedCheck_2233_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2223_);
                    lean_inc(v_date_2222_);
                    lean_dec(v_dt_2220_);
                    v___x_2225_ = lean_box(0);
                    v_isShared_2226_ = v_isSharedCheck_2233_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_month_2227_ = lean_ctor_get(v_date_2222_, 1);
                lean_inc(v_month_2227_);
                v_day_2228_ = lean_ctor_get(v_date_2222_, 2);
                lean_inc(v_day_2228_);
                lean_dec_ref(v_date_2222_);
                v___x_2229_ =
                    l_Std_Time_PlainDate_rollOver(v_year_2221_, v_month_2227_, v_day_2228_);
                lean_dec(v_day_2228_);
                if v_isShared_2226_ == 0 {
                    lean_ctor_set(v___x_2225_, 0, v___x_2229_);
                    v___x_2231_ = v___x_2225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
                    lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_time_2223_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withHours(
    mut v_dt_2234_: *mut LeanObject,
    mut v_hour_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v_minute_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v_unused_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2236_ = lean_ctor_get(v_dt_2234_, 1);
                v_date_2237_ = lean_ctor_get(v_dt_2234_, 0);
                v_isSharedCheck_2255_ = (!lean_is_exclusive(v_dt_2234_)) as u8;
                if v_isSharedCheck_2255_ == 0 {
                    v___x_2239_ = v_dt_2234_;
                    v_isShared_2240_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2236_);
                    lean_inc(v_date_2237_);
                    lean_dec(v_dt_2234_);
                    v___x_2239_ = lean_box(0);
                    v_isShared_2240_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_minute_2241_ = lean_ctor_get(v_time_2236_, 1);
                v_second_2242_ = lean_ctor_get(v_time_2236_, 2);
                v_nanosecond_2243_ = lean_ctor_get(v_time_2236_, 3);
                v_isSharedCheck_2253_ = (!lean_is_exclusive(v_time_2236_)) as u8;
                if v_isSharedCheck_2253_ == 0 {
                    v_unused_2254_ = lean_ctor_get(v_time_2236_, 0);
                    lean_dec(v_unused_2254_);
                    v___x_2245_ = v_time_2236_;
                    v_isShared_2246_ = v_isSharedCheck_2253_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nanosecond_2243_);
                    lean_inc(v_second_2242_);
                    lean_inc(v_minute_2241_);
                    lean_dec(v_time_2236_);
                    v___x_2245_ = lean_box(0);
                    v_isShared_2246_ = v_isSharedCheck_2253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2246_ == 0 {
                    lean_ctor_set(v___x_2245_, 0, v_hour_2235_);
                    v___x_2248_ = v___x_2245_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_hour_2235_);
                    lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_minute_2241_);
                    lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_second_2242_);
                    lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_nanosecond_2243_);
                    v___x_2248_ = v_reuseFailAlloc_2252_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2240_ == 0 {
                    lean_ctor_set(v___x_2239_, 1, v___x_2248_);
                    v___x_2250_ = v___x_2239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_date_2237_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2248_);
                    v___x_2250_ = v_reuseFailAlloc_2251_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withMinutes(
    mut v_dt_2256_: *mut LeanObject,
    mut v_minute_2257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v_hour_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_unused_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2258_ = lean_ctor_get(v_dt_2256_, 1);
                v_date_2259_ = lean_ctor_get(v_dt_2256_, 0);
                v_isSharedCheck_2277_ = (!lean_is_exclusive(v_dt_2256_)) as u8;
                if v_isSharedCheck_2277_ == 0 {
                    v___x_2261_ = v_dt_2256_;
                    v_isShared_2262_ = v_isSharedCheck_2277_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2258_);
                    lean_inc(v_date_2259_);
                    lean_dec(v_dt_2256_);
                    v___x_2261_ = lean_box(0);
                    v_isShared_2262_ = v_isSharedCheck_2277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2263_ = lean_ctor_get(v_time_2258_, 0);
                v_second_2264_ = lean_ctor_get(v_time_2258_, 2);
                v_nanosecond_2265_ = lean_ctor_get(v_time_2258_, 3);
                v_isSharedCheck_2275_ = (!lean_is_exclusive(v_time_2258_)) as u8;
                if v_isSharedCheck_2275_ == 0 {
                    v_unused_2276_ = lean_ctor_get(v_time_2258_, 1);
                    lean_dec(v_unused_2276_);
                    v___x_2267_ = v_time_2258_;
                    v_isShared_2268_ = v_isSharedCheck_2275_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nanosecond_2265_);
                    lean_inc(v_second_2264_);
                    lean_inc(v_hour_2263_);
                    lean_dec(v_time_2258_);
                    v___x_2267_ = lean_box(0);
                    v_isShared_2268_ = v_isSharedCheck_2275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2268_ == 0 {
                    lean_ctor_set(v___x_2267_, 1, v_minute_2257_);
                    v___x_2270_ = v___x_2267_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_hour_2263_);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_minute_2257_);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_second_2264_);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_nanosecond_2265_);
                    v___x_2270_ = v_reuseFailAlloc_2274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2262_ == 0 {
                    lean_ctor_set(v___x_2261_, 1, v___x_2270_);
                    v___x_2272_ = v___x_2261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2273_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_date_2259_);
                    lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2270_);
                    v___x_2272_ = v_reuseFailAlloc_2273_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2272_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withSeconds(
    mut v_dt_2278_: *mut LeanObject,
    mut v_second_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v_hour_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_unused_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2280_ = lean_ctor_get(v_dt_2278_, 1);
                v_date_2281_ = lean_ctor_get(v_dt_2278_, 0);
                v_isSharedCheck_2299_ = (!lean_is_exclusive(v_dt_2278_)) as u8;
                if v_isSharedCheck_2299_ == 0 {
                    v___x_2283_ = v_dt_2278_;
                    v_isShared_2284_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2280_);
                    lean_inc(v_date_2281_);
                    lean_dec(v_dt_2278_);
                    v___x_2283_ = lean_box(0);
                    v_isShared_2284_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2285_ = lean_ctor_get(v_time_2280_, 0);
                v_minute_2286_ = lean_ctor_get(v_time_2280_, 1);
                v_nanosecond_2287_ = lean_ctor_get(v_time_2280_, 3);
                v_isSharedCheck_2297_ = (!lean_is_exclusive(v_time_2280_)) as u8;
                if v_isSharedCheck_2297_ == 0 {
                    v_unused_2298_ = lean_ctor_get(v_time_2280_, 2);
                    lean_dec(v_unused_2298_);
                    v___x_2289_ = v_time_2280_;
                    v_isShared_2290_ = v_isSharedCheck_2297_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nanosecond_2287_);
                    lean_inc(v_minute_2286_);
                    lean_inc(v_hour_2285_);
                    lean_dec(v_time_2280_);
                    v___x_2289_ = lean_box(0);
                    v_isShared_2290_ = v_isSharedCheck_2297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2290_ == 0 {
                    lean_ctor_set(v___x_2289_, 2, v_second_2279_);
                    v___x_2292_ = v___x_2289_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_hour_2285_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_minute_2286_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 2, v_second_2279_);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 3, v_nanosecond_2287_);
                    v___x_2292_ = v_reuseFailAlloc_2296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2284_ == 0 {
                    lean_ctor_set(v___x_2283_, 1, v___x_2292_);
                    v___x_2294_ = v___x_2283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_date_2281_);
                    lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2292_);
                    v___x_2294_ = v_reuseFailAlloc_2295_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0() -> *mut LeanObject {
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2300_ = lean_unsigned_to_nat(1000);
    v___x_2301_ = lean_nat_to_int(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1() -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = lean_unsigned_to_nat(1000000);
    v___x_2303_ = lean_nat_to_int(v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withMilliseconds(
    mut v_dt_2304_: *mut LeanObject,
    mut v_millis_2305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2310_: u8 = 0;
    let mut v_hour_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2306_ = lean_ctor_get(v_dt_2304_, 1);
                v_date_2307_ = lean_ctor_get(v_dt_2304_, 0);
                v_isSharedCheck_2330_ = (!lean_is_exclusive(v_dt_2304_)) as u8;
                if v_isSharedCheck_2330_ == 0 {
                    v___x_2309_ = v_dt_2304_;
                    v_isShared_2310_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2306_);
                    lean_inc(v_date_2307_);
                    lean_dec(v_dt_2304_);
                    v___x_2309_ = lean_box(0);
                    v_isShared_2310_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2311_ = lean_ctor_get(v_time_2306_, 0);
                v_minute_2312_ = lean_ctor_get(v_time_2306_, 1);
                v_second_2313_ = lean_ctor_get(v_time_2306_, 2);
                v_nanosecond_2314_ = lean_ctor_get(v_time_2306_, 3);
                v_isSharedCheck_2329_ = (!lean_is_exclusive(v_time_2306_)) as u8;
                if v_isSharedCheck_2329_ == 0 {
                    v___x_2316_ = v_time_2306_;
                    v_isShared_2317_ = v_isSharedCheck_2329_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_nanosecond_2314_);
                    lean_inc(v_second_2313_);
                    lean_inc(v_minute_2312_);
                    lean_inc(v_hour_2311_);
                    lean_dec(v_time_2306_);
                    v___x_2316_ = lean_box(0);
                    v_isShared_2317_ = v_isSharedCheck_2329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2318_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0,
                );
                v___x_2319_ = lean_int_emod(v_nanosecond_2314_, v___x_2318_);
                lean_dec(v_nanosecond_2314_);
                v___x_2320_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
                );
                v___x_2321_ = lean_int_mul(v_millis_2305_, v___x_2320_);
                v___x_2322_ = lean_int_add(v___x_2321_, v___x_2319_);
                lean_dec(v___x_2319_);
                lean_dec(v___x_2321_);
                if v_isShared_2317_ == 0 {
                    lean_ctor_set(v___x_2316_, 3, v___x_2322_);
                    v___x_2324_ = v___x_2316_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_hour_2311_);
                    lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_minute_2312_);
                    lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_second_2313_);
                    lean_ctor_set(v_reuseFailAlloc_2328_, 3, v___x_2322_);
                    v___x_2324_ = v_reuseFailAlloc_2328_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2310_ == 0 {
                    lean_ctor_set(v___x_2309_, 1, v___x_2324_);
                    v___x_2326_ = v___x_2309_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_date_2307_);
                    lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2324_);
                    v___x_2326_ = v_reuseFailAlloc_2327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withMilliseconds___boxed(
    mut v_dt_2331_: *mut LeanObject,
    mut v_millis_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2333_: *mut LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_2331_, v_millis_2332_);
    lean_dec(v_millis_2332_);
    return v_res_2333_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withNanoseconds(
    mut v_dt_2334_: *mut LeanObject,
    mut v_nano_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v_hour_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2353_: u8 = 0;
    let mut v_unused_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2336_ = lean_ctor_get(v_dt_2334_, 1);
                v_date_2337_ = lean_ctor_get(v_dt_2334_, 0);
                v_isSharedCheck_2355_ = (!lean_is_exclusive(v_dt_2334_)) as u8;
                if v_isSharedCheck_2355_ == 0 {
                    v___x_2339_ = v_dt_2334_;
                    v_isShared_2340_ = v_isSharedCheck_2355_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2336_);
                    lean_inc(v_date_2337_);
                    lean_dec(v_dt_2334_);
                    v___x_2339_ = lean_box(0);
                    v_isShared_2340_ = v_isSharedCheck_2355_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2341_ = lean_ctor_get(v_time_2336_, 0);
                v_minute_2342_ = lean_ctor_get(v_time_2336_, 1);
                v_second_2343_ = lean_ctor_get(v_time_2336_, 2);
                v_isSharedCheck_2353_ = (!lean_is_exclusive(v_time_2336_)) as u8;
                if v_isSharedCheck_2353_ == 0 {
                    v_unused_2354_ = lean_ctor_get(v_time_2336_, 3);
                    lean_dec(v_unused_2354_);
                    v___x_2345_ = v_time_2336_;
                    v_isShared_2346_ = v_isSharedCheck_2353_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_second_2343_);
                    lean_inc(v_minute_2342_);
                    lean_inc(v_hour_2341_);
                    lean_dec(v_time_2336_);
                    v___x_2345_ = lean_box(0);
                    v_isShared_2346_ = v_isSharedCheck_2353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2346_ == 0 {
                    lean_ctor_set(v___x_2345_, 3, v_nano_2335_);
                    v___x_2348_ = v___x_2345_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_hour_2341_);
                    lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_minute_2342_);
                    lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_second_2343_);
                    lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_nano_2335_);
                    v___x_2348_ = v_reuseFailAlloc_2352_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2340_ == 0 {
                    lean_ctor_set(v___x_2339_, 1, v___x_2348_);
                    v___x_2350_ = v___x_2339_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_date_2337_);
                    lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2348_);
                    v___x_2350_ = v_reuseFailAlloc_2351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_addDays(
    mut v_dt_2356_: *mut LeanObject,
    mut v_days_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v_dateDays_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2358_ = lean_ctor_get(v_dt_2356_, 0);
                v_time_2359_ = lean_ctor_get(v_dt_2356_, 1);
                v_isSharedCheck_2369_ = (!lean_is_exclusive(v_dt_2356_)) as u8;
                if v_isSharedCheck_2369_ == 0 {
                    v___x_2361_ = v_dt_2356_;
                    v_isShared_2362_ = v_isSharedCheck_2369_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2359_);
                    lean_inc(v_date_2358_);
                    lean_dec(v_dt_2356_);
                    v___x_2361_ = lean_box(0);
                    v_isShared_2362_ = v_isSharedCheck_2369_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dateDays_2363_ = l_Std_Time_PlainDate_toEpochDay(v_date_2358_);
                v___x_2364_ = lean_int_add(v_dateDays_2363_, v_days_2357_);
                lean_dec(v_dateDays_2363_);
                v___x_2365_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2364_);
                lean_dec(v___x_2364_);
                if v_isShared_2362_ == 0 {
                    lean_ctor_set(v___x_2361_, 0, v___x_2365_);
                    v___x_2367_ = v___x_2361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
                    lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_time_2359_);
                    v___x_2367_ = v_reuseFailAlloc_2368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_addDays___boxed(
    mut v_dt_2370_: *mut LeanObject,
    mut v_days_2371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2372_: *mut LeanObject = core::ptr::null_mut();
    v_res_2372_ = l_Std_Time_PlainDateTime_addDays(v_dt_2370_, v_days_2371_);
    lean_dec(v_days_2371_);
    return v_res_2372_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subDays(
    mut v_dt_2373_: *mut LeanObject,
    mut v_days_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dateDays_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2375_ = lean_ctor_get(v_dt_2373_, 0);
                v_time_2376_ = lean_ctor_get(v_dt_2373_, 1);
                v_isSharedCheck_2387_ = (!lean_is_exclusive(v_dt_2373_)) as u8;
                if v_isSharedCheck_2387_ == 0 {
                    v___x_2378_ = v_dt_2373_;
                    v_isShared_2379_ = v_isSharedCheck_2387_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2376_);
                    lean_inc(v_date_2375_);
                    lean_dec(v_dt_2373_);
                    v___x_2378_ = lean_box(0);
                    v_isShared_2379_ = v_isSharedCheck_2387_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2380_ = lean_int_neg(v_days_2374_);
                v_dateDays_2381_ = l_Std_Time_PlainDate_toEpochDay(v_date_2375_);
                v___x_2382_ = lean_int_add(v_dateDays_2381_, v___x_2380_);
                lean_dec(v___x_2380_);
                lean_dec(v_dateDays_2381_);
                v___x_2383_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2382_);
                lean_dec(v___x_2382_);
                if v_isShared_2379_ == 0 {
                    lean_ctor_set(v___x_2378_, 0, v___x_2383_);
                    v___x_2385_ = v___x_2378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_time_2376_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_subDays___boxed(
    mut v_dt_2388_: *mut LeanObject,
    mut v_days_2389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2390_: *mut LeanObject = core::ptr::null_mut();
    v_res_2390_ = l_Std_Time_PlainDateTime_subDays(v_dt_2388_, v_days_2389_);
    lean_dec(v_days_2389_);
    return v_res_2390_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2391_ = lean_unsigned_to_nat(7);
    v___x_2392_ = lean_nat_to_int(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addWeeks(
    mut v_dt_2393_: *mut LeanObject,
    mut v_weeks_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v_dateDays_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2395_ = lean_ctor_get(v_dt_2393_, 0);
                v_time_2396_ = lean_ctor_get(v_dt_2393_, 1);
                v_isSharedCheck_2408_ = (!lean_is_exclusive(v_dt_2393_)) as u8;
                if v_isSharedCheck_2408_ == 0 {
                    v___x_2398_ = v_dt_2393_;
                    v_isShared_2399_ = v_isSharedCheck_2408_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2396_);
                    lean_inc(v_date_2395_);
                    lean_dec(v_dt_2393_);
                    v___x_2398_ = lean_box(0);
                    v_isShared_2399_ = v_isSharedCheck_2408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dateDays_2400_ = l_Std_Time_PlainDate_toEpochDay(v_date_2395_);
                v___x_2401_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_addWeeks___closed__0,
                );
                v_daysToAdd_2402_ = lean_int_mul(v_weeks_2394_, v___x_2401_);
                v___x_2403_ = lean_int_add(v_dateDays_2400_, v_daysToAdd_2402_);
                lean_dec(v_daysToAdd_2402_);
                lean_dec(v_dateDays_2400_);
                v___x_2404_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2403_);
                lean_dec(v___x_2403_);
                if v_isShared_2399_ == 0 {
                    lean_ctor_set(v___x_2398_, 0, v___x_2404_);
                    v___x_2406_ = v___x_2398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
                    lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_time_2396_);
                    v___x_2406_ = v_reuseFailAlloc_2407_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2406_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_addWeeks___boxed(
    mut v_dt_2409_: *mut LeanObject,
    mut v_weeks_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2411_: *mut LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_2409_, v_weeks_2410_);
    lean_dec(v_weeks_2410_);
    return v_res_2411_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subWeeks(
    mut v_dt_2412_: *mut LeanObject,
    mut v_weeks_2413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2418_: u8 = 0;
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dateDays_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2414_ = lean_ctor_get(v_dt_2412_, 0);
                v_time_2415_ = lean_ctor_get(v_dt_2412_, 1);
                v_isSharedCheck_2428_ = (!lean_is_exclusive(v_dt_2412_)) as u8;
                if v_isSharedCheck_2428_ == 0 {
                    v___x_2417_ = v_dt_2412_;
                    v_isShared_2418_ = v_isSharedCheck_2428_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2415_);
                    lean_inc(v_date_2414_);
                    lean_dec(v_dt_2412_);
                    v___x_2417_ = lean_box(0);
                    v_isShared_2418_ = v_isSharedCheck_2428_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2419_ = lean_int_neg(v_weeks_2413_);
                v_dateDays_2420_ = l_Std_Time_PlainDate_toEpochDay(v_date_2414_);
                v___x_2421_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_addWeeks___closed__0,
                );
                v_daysToAdd_2422_ = lean_int_mul(v___x_2419_, v___x_2421_);
                lean_dec(v___x_2419_);
                v___x_2423_ = lean_int_add(v_dateDays_2420_, v_daysToAdd_2422_);
                lean_dec(v_daysToAdd_2422_);
                lean_dec(v_dateDays_2420_);
                v___x_2424_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2423_);
                lean_dec(v___x_2423_);
                if v_isShared_2418_ == 0 {
                    lean_ctor_set(v___x_2417_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2417_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_time_2415_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_subWeeks___boxed(
    mut v_dt_2429_: *mut LeanObject,
    mut v_weeks_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2431_: *mut LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_2429_, v_weeks_2430_);
    lean_dec(v_weeks_2430_);
    return v_res_2431_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMonthsClip(
    mut v_dt_2432_: *mut LeanObject,
    mut v_months_2433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2438_: u8 = 0;
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2434_ = lean_ctor_get(v_dt_2432_, 0);
                v_time_2435_ = lean_ctor_get(v_dt_2432_, 1);
                v_isSharedCheck_2443_ = (!lean_is_exclusive(v_dt_2432_)) as u8;
                if v_isSharedCheck_2443_ == 0 {
                    v___x_2437_ = v_dt_2432_;
                    v_isShared_2438_ = v_isSharedCheck_2443_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2435_);
                    lean_inc(v_date_2434_);
                    lean_dec(v_dt_2432_);
                    v___x_2437_ = lean_box(0);
                    v_isShared_2438_ = v_isSharedCheck_2443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2439_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2434_, v_months_2433_);
                if v_isShared_2438_ == 0 {
                    lean_ctor_set(v___x_2437_, 0, v___x_2439_);
                    v___x_2441_ = v___x_2437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
                    lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_time_2435_);
                    v___x_2441_ = v_reuseFailAlloc_2442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_addMonthsClip___boxed(
    mut v_dt_2444_: *mut LeanObject,
    mut v_months_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2446_: *mut LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_2444_, v_months_2445_);
    lean_dec(v_months_2445_);
    return v_res_2446_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMonthsClip(
    mut v_dt_2447_: *mut LeanObject,
    mut v_months_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2449_ = lean_ctor_get(v_dt_2447_, 0);
                v_time_2450_ = lean_ctor_get(v_dt_2447_, 1);
                v_isSharedCheck_2459_ = (!lean_is_exclusive(v_dt_2447_)) as u8;
                if v_isSharedCheck_2459_ == 0 {
                    v___x_2452_ = v_dt_2447_;
                    v_isShared_2453_ = v_isSharedCheck_2459_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2450_);
                    lean_inc(v_date_2449_);
                    lean_dec(v_dt_2447_);
                    v___x_2452_ = lean_box(0);
                    v_isShared_2453_ = v_isSharedCheck_2459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2454_ = lean_int_neg(v_months_2448_);
                v___x_2455_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2449_, v___x_2454_);
                lean_dec(v___x_2454_);
                if v_isShared_2453_ == 0 {
                    lean_ctor_set(v___x_2452_, 0, v___x_2455_);
                    v___x_2457_ = v___x_2452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
                    lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_time_2450_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_subMonthsClip___boxed(
    mut v_dt_2460_: *mut LeanObject,
    mut v_months_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2462_: *mut LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_2460_, v_months_2461_);
    lean_dec(v_months_2461_);
    return v_res_2462_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMonthsRollOver(
    mut v_dt_2463_: *mut LeanObject,
    mut v_months_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2465_ = lean_ctor_get(v_dt_2463_, 0);
                v_time_2466_ = lean_ctor_get(v_dt_2463_, 1);
                v_isSharedCheck_2474_ = (!lean_is_exclusive(v_dt_2463_)) as u8;
                if v_isSharedCheck_2474_ == 0 {
                    v___x_2468_ = v_dt_2463_;
                    v_isShared_2469_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2466_);
                    lean_inc(v_date_2465_);
                    lean_dec(v_dt_2463_);
                    v___x_2468_ = lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2470_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2465_, v_months_2464_);
                if v_isShared_2469_ == 0 {
                    lean_ctor_set(v___x_2468_, 0, v___x_2470_);
                    v___x_2472_ = v___x_2468_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
                    lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_time_2466_);
                    v___x_2472_ = v_reuseFailAlloc_2473_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_addMonthsRollOver___boxed(
    mut v_dt_2475_: *mut LeanObject,
    mut v_months_2476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2477_: *mut LeanObject = core::ptr::null_mut();
    v_res_2477_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_2475_, v_months_2476_);
    lean_dec(v_months_2476_);
    return v_res_2477_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMonthsRollOver(
    mut v_dt_2478_: *mut LeanObject,
    mut v_months_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2484_: u8 = 0;
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2480_ = lean_ctor_get(v_dt_2478_, 0);
                v_time_2481_ = lean_ctor_get(v_dt_2478_, 1);
                v_isSharedCheck_2490_ = (!lean_is_exclusive(v_dt_2478_)) as u8;
                if v_isSharedCheck_2490_ == 0 {
                    v___x_2483_ = v_dt_2478_;
                    v_isShared_2484_ = v_isSharedCheck_2490_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2481_);
                    lean_inc(v_date_2480_);
                    lean_dec(v_dt_2478_);
                    v___x_2483_ = lean_box(0);
                    v_isShared_2484_ = v_isSharedCheck_2490_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2485_ = lean_int_neg(v_months_2479_);
                v___x_2486_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2480_, v___x_2485_);
                lean_dec(v___x_2485_);
                if v_isShared_2484_ == 0 {
                    lean_ctor_set(v___x_2483_, 0, v___x_2486_);
                    v___x_2488_ = v___x_2483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
                    lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_time_2481_);
                    v___x_2488_ = v_reuseFailAlloc_2489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2488_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_subMonthsRollOver___boxed(
    mut v_dt_2491_: *mut LeanObject,
    mut v_months_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_2491_, v_months_2492_);
    lean_dec(v_months_2492_);
    return v_res_2493_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0() -> *mut LeanObject {
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    v___x_2494_ = lean_unsigned_to_nat(12);
    v___x_2495_ = lean_nat_to_int(v___x_2494_);
    return v___x_2495_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addYearsRollOver(
    mut v_dt_2496_: *mut LeanObject,
    mut v_years_2497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2498_ = lean_ctor_get(v_dt_2496_, 0);
                v_time_2499_ = lean_ctor_get(v_dt_2496_, 1);
                v_isSharedCheck_2509_ = (!lean_is_exclusive(v_dt_2496_)) as u8;
                if v_isSharedCheck_2509_ == 0 {
                    v___x_2501_ = v_dt_2496_;
                    v_isShared_2502_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2499_);
                    lean_inc(v_date_2498_);
                    lean_dec(v_dt_2496_);
                    v___x_2501_ = lean_box(0);
                    v_isShared_2502_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2503_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2504_ = lean_int_mul(v_years_2497_, v___x_2503_);
                v___x_2505_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2498_, v___x_2504_);
                lean_dec(v___x_2504_);
                if v_isShared_2502_ == 0 {
                    lean_ctor_set(v___x_2501_, 0, v___x_2505_);
                    v___x_2507_ = v___x_2501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
                    lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_time_2499_);
                    v___x_2507_ = v_reuseFailAlloc_2508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_addYearsRollOver___boxed(
    mut v_dt_2510_: *mut LeanObject,
    mut v_years_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2512_: *mut LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_2510_, v_years_2511_);
    lean_dec(v_years_2511_);
    return v_res_2512_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addYearsClip(
    mut v_dt_2513_: *mut LeanObject,
    mut v_years_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2519_: u8 = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2515_ = lean_ctor_get(v_dt_2513_, 0);
                v_time_2516_ = lean_ctor_get(v_dt_2513_, 1);
                v_isSharedCheck_2526_ = (!lean_is_exclusive(v_dt_2513_)) as u8;
                if v_isSharedCheck_2526_ == 0 {
                    v___x_2518_ = v_dt_2513_;
                    v_isShared_2519_ = v_isSharedCheck_2526_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2516_);
                    lean_inc(v_date_2515_);
                    lean_dec(v_dt_2513_);
                    v___x_2518_ = lean_box(0);
                    v_isShared_2519_ = v_isSharedCheck_2526_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2520_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2521_ = lean_int_mul(v_years_2514_, v___x_2520_);
                v___x_2522_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2515_, v___x_2521_);
                lean_dec(v___x_2521_);
                if v_isShared_2519_ == 0 {
                    lean_ctor_set(v___x_2518_, 0, v___x_2522_);
                    v___x_2524_ = v___x_2518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
                    lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_time_2516_);
                    v___x_2524_ = v_reuseFailAlloc_2525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2524_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_addYearsClip___boxed(
    mut v_dt_2527_: *mut LeanObject,
    mut v_years_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2529_: *mut LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_2527_, v_years_2528_);
    lean_dec(v_years_2528_);
    return v_res_2529_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subYearsRollOver(
    mut v_dt_2530_: *mut LeanObject,
    mut v_years_2531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2532_ = lean_ctor_get(v_dt_2530_, 0);
                v_time_2533_ = lean_ctor_get(v_dt_2530_, 1);
                v_isSharedCheck_2544_ = (!lean_is_exclusive(v_dt_2530_)) as u8;
                if v_isSharedCheck_2544_ == 0 {
                    v___x_2535_ = v_dt_2530_;
                    v_isShared_2536_ = v_isSharedCheck_2544_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2533_);
                    lean_inc(v_date_2532_);
                    lean_dec(v_dt_2530_);
                    v___x_2535_ = lean_box(0);
                    v_isShared_2536_ = v_isSharedCheck_2544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2537_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2538_ = lean_int_mul(v_years_2531_, v___x_2537_);
                v___x_2539_ = lean_int_neg(v___x_2538_);
                lean_dec(v___x_2538_);
                v___x_2540_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2532_, v___x_2539_);
                lean_dec(v___x_2539_);
                if v_isShared_2536_ == 0 {
                    lean_ctor_set(v___x_2535_, 0, v___x_2540_);
                    v___x_2542_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_time_2533_);
                    v___x_2542_ = v_reuseFailAlloc_2543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_subYearsRollOver___boxed(
    mut v_dt_2545_: *mut LeanObject,
    mut v_years_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2547_: *mut LeanObject = core::ptr::null_mut();
    v_res_2547_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_2545_, v_years_2546_);
    lean_dec(v_years_2546_);
    return v_res_2547_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subYearsClip(
    mut v_dt_2548_: *mut LeanObject,
    mut v_years_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2554_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2550_ = lean_ctor_get(v_dt_2548_, 0);
                v_time_2551_ = lean_ctor_get(v_dt_2548_, 1);
                v_isSharedCheck_2562_ = (!lean_is_exclusive(v_dt_2548_)) as u8;
                if v_isSharedCheck_2562_ == 0 {
                    v___x_2553_ = v_dt_2548_;
                    v_isShared_2554_ = v_isSharedCheck_2562_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_time_2551_);
                    lean_inc(v_date_2550_);
                    lean_dec(v_dt_2548_);
                    v___x_2553_ = lean_box(0);
                    v_isShared_2554_ = v_isSharedCheck_2562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2555_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2556_ = lean_int_mul(v_years_2549_, v___x_2555_);
                v___x_2557_ = lean_int_neg(v___x_2556_);
                lean_dec(v___x_2556_);
                v___x_2558_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2550_, v___x_2557_);
                lean_dec(v___x_2557_);
                if v_isShared_2554_ == 0 {
                    lean_ctor_set(v___x_2553_, 0, v___x_2558_);
                    v___x_2560_ = v___x_2553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
                    lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_time_2551_);
                    v___x_2560_ = v_reuseFailAlloc_2561_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2560_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_subYearsClip___boxed(
    mut v_dt_2563_: *mut LeanObject,
    mut v_years_2564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2565_: *mut LeanObject = core::ptr::null_mut();
    v_res_2565_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_2563_, v_years_2564_);
    lean_dec(v_years_2564_);
    return v_res_2565_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addNanoseconds(
    mut v_dt_2566_: *mut LeanObject,
    mut v_nanos_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v___x_2568_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2566_);
    v_second_2569_ = lean_ctor_get(v___x_2568_, 0);
    lean_inc(v_second_2569_);
    v_nano_2570_ = lean_ctor_get(v___x_2568_, 1);
    lean_inc(v_nano_2570_);
    lean_dec_ref(v___x_2568_);
    v___x_2571_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_2567_);
    v_second_2572_ = lean_ctor_get(v___x_2571_, 0);
    lean_inc(v_second_2572_);
    v_nano_2573_ = lean_ctor_get(v___x_2571_, 1);
    lean_inc(v_nano_2573_);
    lean_dec_ref(v___x_2571_);
    v___x_2574_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2575_ = lean_int_mul(v_second_2569_, v___x_2574_);
    lean_dec(v_second_2569_);
    v___x_2576_ = lean_int_add(v___x_2575_, v_nano_2570_);
    lean_dec(v_nano_2570_);
    lean_dec(v___x_2575_);
    v___x_2577_ = lean_int_mul(v_second_2572_, v___x_2574_);
    lean_dec(v_second_2572_);
    v___x_2578_ = lean_int_add(v___x_2577_, v_nano_2573_);
    lean_dec(v_nano_2573_);
    lean_dec(v___x_2577_);
    v___x_2579_ = lean_int_add(v___x_2576_, v___x_2578_);
    lean_dec(v___x_2578_);
    lean_dec(v___x_2576_);
    v___x_2580_ = l_Std_Time_Duration_ofNanoseconds(v___x_2579_);
    lean_dec(v___x_2579_);
    v___x_2581_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2580_);
    return v___x_2581_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addNanoseconds___boxed(
    mut v_dt_2582_: *mut LeanObject,
    mut v_nanos_2583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2584_: *mut LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_2582_, v_nanos_2583_);
    lean_dec(v_nanos_2583_);
    return v_res_2584_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subNanoseconds(
    mut v_dt_2585_: *mut LeanObject,
    mut v_nanos_2586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    v___x_2587_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2585_);
    v_second_2588_ = lean_ctor_get(v___x_2587_, 0);
    lean_inc(v_second_2588_);
    v_nano_2589_ = lean_ctor_get(v___x_2587_, 1);
    lean_inc(v_nano_2589_);
    lean_dec_ref(v___x_2587_);
    v___x_2590_ = lean_int_neg(v_nanos_2586_);
    v___x_2591_ = l_Std_Time_Duration_ofNanoseconds(v___x_2590_);
    lean_dec(v___x_2590_);
    v_second_2592_ = lean_ctor_get(v___x_2591_, 0);
    lean_inc(v_second_2592_);
    v_nano_2593_ = lean_ctor_get(v___x_2591_, 1);
    lean_inc(v_nano_2593_);
    lean_dec_ref(v___x_2591_);
    v___x_2594_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2595_ = lean_int_mul(v_second_2588_, v___x_2594_);
    lean_dec(v_second_2588_);
    v___x_2596_ = lean_int_add(v___x_2595_, v_nano_2589_);
    lean_dec(v_nano_2589_);
    lean_dec(v___x_2595_);
    v___x_2597_ = lean_int_mul(v_second_2592_, v___x_2594_);
    lean_dec(v_second_2592_);
    v___x_2598_ = lean_int_add(v___x_2597_, v_nano_2593_);
    lean_dec(v_nano_2593_);
    lean_dec(v___x_2597_);
    v___x_2599_ = lean_int_add(v___x_2596_, v___x_2598_);
    lean_dec(v___x_2598_);
    lean_dec(v___x_2596_);
    v___x_2600_ = l_Std_Time_Duration_ofNanoseconds(v___x_2599_);
    lean_dec(v___x_2599_);
    v___x_2601_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2600_);
    return v___x_2601_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subNanoseconds___boxed(
    mut v_dt_2602_: *mut LeanObject,
    mut v_nanos_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2604_: *mut LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_2602_, v_nanos_2603_);
    lean_dec(v_nanos_2603_);
    return v_res_2604_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addHours___closed__0() -> *mut LeanObject {
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    v___x_2605_ = lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_2606_ = lean_nat_to_int(v___x_2605_);
    return v___x_2606_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addHours(
    mut v_dt_2607_: *mut LeanObject,
    mut v_hours_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut LeanObject = core::ptr::null_mut();
    v___x_2609_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2607_);
    v_second_2610_ = lean_ctor_get(v___x_2609_, 0);
    lean_inc(v_second_2610_);
    v_nano_2611_ = lean_ctor_get(v___x_2609_, 1);
    lean_inc(v_nano_2611_);
    lean_dec_ref(v___x_2609_);
    v___x_2612_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addHours___closed__0,
    );
    v___x_2613_ = lean_int_mul(v_hours_2608_, v___x_2612_);
    v___x_2614_ = l_Std_Time_Duration_ofNanoseconds(v___x_2613_);
    lean_dec(v___x_2613_);
    v_second_2615_ = lean_ctor_get(v___x_2614_, 0);
    lean_inc(v_second_2615_);
    v_nano_2616_ = lean_ctor_get(v___x_2614_, 1);
    lean_inc(v_nano_2616_);
    lean_dec_ref(v___x_2614_);
    v___x_2617_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2618_ = lean_int_mul(v_second_2610_, v___x_2617_);
    lean_dec(v_second_2610_);
    v___x_2619_ = lean_int_add(v___x_2618_, v_nano_2611_);
    lean_dec(v_nano_2611_);
    lean_dec(v___x_2618_);
    v___x_2620_ = lean_int_mul(v_second_2615_, v___x_2617_);
    lean_dec(v_second_2615_);
    v___x_2621_ = lean_int_add(v___x_2620_, v_nano_2616_);
    lean_dec(v_nano_2616_);
    lean_dec(v___x_2620_);
    v___x_2622_ = lean_int_add(v___x_2619_, v___x_2621_);
    lean_dec(v___x_2621_);
    lean_dec(v___x_2619_);
    v___x_2623_ = l_Std_Time_Duration_ofNanoseconds(v___x_2622_);
    lean_dec(v___x_2622_);
    v___x_2624_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2623_);
    return v___x_2624_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addHours___boxed(
    mut v_dt_2625_: *mut LeanObject,
    mut v_hours_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2627_: *mut LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Std_Time_PlainDateTime_addHours(v_dt_2625_, v_hours_2626_);
    lean_dec(v_hours_2626_);
    return v_res_2627_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subHours(
    mut v_dt_2628_: *mut LeanObject,
    mut v_hours_2629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    v___x_2630_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2628_);
    v_second_2631_ = lean_ctor_get(v___x_2630_, 0);
    lean_inc(v_second_2631_);
    v_nano_2632_ = lean_ctor_get(v___x_2630_, 1);
    lean_inc(v_nano_2632_);
    lean_dec_ref(v___x_2630_);
    v___x_2633_ = lean_int_neg(v_hours_2629_);
    v___x_2634_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addHours___closed__0,
    );
    v___x_2635_ = lean_int_mul(v___x_2633_, v___x_2634_);
    lean_dec(v___x_2633_);
    v___x_2636_ = l_Std_Time_Duration_ofNanoseconds(v___x_2635_);
    lean_dec(v___x_2635_);
    v_second_2637_ = lean_ctor_get(v___x_2636_, 0);
    lean_inc(v_second_2637_);
    v_nano_2638_ = lean_ctor_get(v___x_2636_, 1);
    lean_inc(v_nano_2638_);
    lean_dec_ref(v___x_2636_);
    v___x_2639_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2640_ = lean_int_mul(v_second_2631_, v___x_2639_);
    lean_dec(v_second_2631_);
    v___x_2641_ = lean_int_add(v___x_2640_, v_nano_2632_);
    lean_dec(v_nano_2632_);
    lean_dec(v___x_2640_);
    v___x_2642_ = lean_int_mul(v_second_2637_, v___x_2639_);
    lean_dec(v_second_2637_);
    v___x_2643_ = lean_int_add(v___x_2642_, v_nano_2638_);
    lean_dec(v_nano_2638_);
    lean_dec(v___x_2642_);
    v___x_2644_ = lean_int_add(v___x_2641_, v___x_2643_);
    lean_dec(v___x_2643_);
    lean_dec(v___x_2641_);
    v___x_2645_ = l_Std_Time_Duration_ofNanoseconds(v___x_2644_);
    lean_dec(v___x_2644_);
    v___x_2646_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subHours___boxed(
    mut v_dt_2647_: *mut LeanObject,
    mut v_hours_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2649_: *mut LeanObject = core::ptr::null_mut();
    v_res_2649_ = l_Std_Time_PlainDateTime_subHours(v_dt_2647_, v_hours_2648_);
    lean_dec(v_hours_2648_);
    return v_res_2649_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addMinutes___closed__0() -> *mut LeanObject {
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    v___x_2650_ = lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_2651_ = lean_nat_to_int(v___x_2650_);
    return v___x_2651_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMinutes(
    mut v_dt_2652_: *mut LeanObject,
    mut v_minutes_2653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    v___x_2654_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2652_);
    v_second_2655_ = lean_ctor_get(v___x_2654_, 0);
    lean_inc(v_second_2655_);
    v_nano_2656_ = lean_ctor_get(v___x_2654_, 1);
    lean_inc(v_nano_2656_);
    lean_dec_ref(v___x_2654_);
    v___x_2657_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addMinutes___closed__0,
    );
    v___x_2658_ = lean_int_mul(v_minutes_2653_, v___x_2657_);
    v___x_2659_ = l_Std_Time_Duration_ofNanoseconds(v___x_2658_);
    lean_dec(v___x_2658_);
    v_second_2660_ = lean_ctor_get(v___x_2659_, 0);
    lean_inc(v_second_2660_);
    v_nano_2661_ = lean_ctor_get(v___x_2659_, 1);
    lean_inc(v_nano_2661_);
    lean_dec_ref(v___x_2659_);
    v___x_2662_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2663_ = lean_int_mul(v_second_2655_, v___x_2662_);
    lean_dec(v_second_2655_);
    v___x_2664_ = lean_int_add(v___x_2663_, v_nano_2656_);
    lean_dec(v_nano_2656_);
    lean_dec(v___x_2663_);
    v___x_2665_ = lean_int_mul(v_second_2660_, v___x_2662_);
    lean_dec(v_second_2660_);
    v___x_2666_ = lean_int_add(v___x_2665_, v_nano_2661_);
    lean_dec(v_nano_2661_);
    lean_dec(v___x_2665_);
    v___x_2667_ = lean_int_add(v___x_2664_, v___x_2666_);
    lean_dec(v___x_2666_);
    lean_dec(v___x_2664_);
    v___x_2668_ = l_Std_Time_Duration_ofNanoseconds(v___x_2667_);
    lean_dec(v___x_2667_);
    v___x_2669_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2668_);
    return v___x_2669_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMinutes___boxed(
    mut v_dt_2670_: *mut LeanObject,
    mut v_minutes_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2672_: *mut LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_2670_, v_minutes_2671_);
    lean_dec(v_minutes_2671_);
    return v_res_2672_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMinutes(
    mut v_dt_2673_: *mut LeanObject,
    mut v_minutes_2674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    v___x_2675_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2673_);
    v_second_2676_ = lean_ctor_get(v___x_2675_, 0);
    lean_inc(v_second_2676_);
    v_nano_2677_ = lean_ctor_get(v___x_2675_, 1);
    lean_inc(v_nano_2677_);
    lean_dec_ref(v___x_2675_);
    v___x_2678_ = lean_int_neg(v_minutes_2674_);
    v___x_2679_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addMinutes___closed__0,
    );
    v___x_2680_ = lean_int_mul(v___x_2678_, v___x_2679_);
    lean_dec(v___x_2678_);
    v___x_2681_ = l_Std_Time_Duration_ofNanoseconds(v___x_2680_);
    lean_dec(v___x_2680_);
    v_second_2682_ = lean_ctor_get(v___x_2681_, 0);
    lean_inc(v_second_2682_);
    v_nano_2683_ = lean_ctor_get(v___x_2681_, 1);
    lean_inc(v_nano_2683_);
    lean_dec_ref(v___x_2681_);
    v___x_2684_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2685_ = lean_int_mul(v_second_2676_, v___x_2684_);
    lean_dec(v_second_2676_);
    v___x_2686_ = lean_int_add(v___x_2685_, v_nano_2677_);
    lean_dec(v_nano_2677_);
    lean_dec(v___x_2685_);
    v___x_2687_ = lean_int_mul(v_second_2682_, v___x_2684_);
    lean_dec(v_second_2682_);
    v___x_2688_ = lean_int_add(v___x_2687_, v_nano_2683_);
    lean_dec(v_nano_2683_);
    lean_dec(v___x_2687_);
    v___x_2689_ = lean_int_add(v___x_2686_, v___x_2688_);
    lean_dec(v___x_2688_);
    lean_dec(v___x_2686_);
    v___x_2690_ = l_Std_Time_Duration_ofNanoseconds(v___x_2689_);
    lean_dec(v___x_2689_);
    v___x_2691_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2690_);
    return v___x_2691_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMinutes___boxed(
    mut v_dt_2692_: *mut LeanObject,
    mut v_minutes_2693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2694_: *mut LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_2692_, v_minutes_2693_);
    lean_dec(v_minutes_2693_);
    return v_res_2694_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addSeconds(
    mut v_dt_2695_: *mut LeanObject,
    mut v_seconds_2696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    v___x_2697_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2695_);
    v_second_2698_ = lean_ctor_get(v___x_2697_, 0);
    lean_inc(v_second_2698_);
    v_nano_2699_ = lean_ctor_get(v___x_2697_, 1);
    lean_inc(v_nano_2699_);
    lean_dec_ref(v___x_2697_);
    v___x_2700_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2701_ = lean_int_mul(v_seconds_2696_, v___x_2700_);
    v___x_2702_ = l_Std_Time_Duration_ofNanoseconds(v___x_2701_);
    lean_dec(v___x_2701_);
    v_second_2703_ = lean_ctor_get(v___x_2702_, 0);
    lean_inc(v_second_2703_);
    v_nano_2704_ = lean_ctor_get(v___x_2702_, 1);
    lean_inc(v_nano_2704_);
    lean_dec_ref(v___x_2702_);
    v___x_2705_ = lean_int_mul(v_second_2698_, v___x_2700_);
    lean_dec(v_second_2698_);
    v___x_2706_ = lean_int_add(v___x_2705_, v_nano_2699_);
    lean_dec(v_nano_2699_);
    lean_dec(v___x_2705_);
    v___x_2707_ = lean_int_mul(v_second_2703_, v___x_2700_);
    lean_dec(v_second_2703_);
    v___x_2708_ = lean_int_add(v___x_2707_, v_nano_2704_);
    lean_dec(v_nano_2704_);
    lean_dec(v___x_2707_);
    v___x_2709_ = lean_int_add(v___x_2706_, v___x_2708_);
    lean_dec(v___x_2708_);
    lean_dec(v___x_2706_);
    v___x_2710_ = l_Std_Time_Duration_ofNanoseconds(v___x_2709_);
    lean_dec(v___x_2709_);
    v___x_2711_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2710_);
    return v___x_2711_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addSeconds___boxed(
    mut v_dt_2712_: *mut LeanObject,
    mut v_seconds_2713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2714_: *mut LeanObject = core::ptr::null_mut();
    v_res_2714_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_2712_, v_seconds_2713_);
    lean_dec(v_seconds_2713_);
    return v_res_2714_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subSeconds(
    mut v_dt_2715_: *mut LeanObject,
    mut v_seconds_2716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    v___x_2717_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2715_);
    v_second_2718_ = lean_ctor_get(v___x_2717_, 0);
    lean_inc(v_second_2718_);
    v_nano_2719_ = lean_ctor_get(v___x_2717_, 1);
    lean_inc(v_nano_2719_);
    lean_dec_ref(v___x_2717_);
    v___x_2720_ = lean_int_neg(v_seconds_2716_);
    v___x_2721_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2722_ = lean_int_mul(v___x_2720_, v___x_2721_);
    lean_dec(v___x_2720_);
    v___x_2723_ = l_Std_Time_Duration_ofNanoseconds(v___x_2722_);
    lean_dec(v___x_2722_);
    v_second_2724_ = lean_ctor_get(v___x_2723_, 0);
    lean_inc(v_second_2724_);
    v_nano_2725_ = lean_ctor_get(v___x_2723_, 1);
    lean_inc(v_nano_2725_);
    lean_dec_ref(v___x_2723_);
    v___x_2726_ = lean_int_mul(v_second_2718_, v___x_2721_);
    lean_dec(v_second_2718_);
    v___x_2727_ = lean_int_add(v___x_2726_, v_nano_2719_);
    lean_dec(v_nano_2719_);
    lean_dec(v___x_2726_);
    v___x_2728_ = lean_int_mul(v_second_2724_, v___x_2721_);
    lean_dec(v_second_2724_);
    v___x_2729_ = lean_int_add(v___x_2728_, v_nano_2725_);
    lean_dec(v_nano_2725_);
    lean_dec(v___x_2728_);
    v___x_2730_ = lean_int_add(v___x_2727_, v___x_2729_);
    lean_dec(v___x_2729_);
    lean_dec(v___x_2727_);
    v___x_2731_ = l_Std_Time_Duration_ofNanoseconds(v___x_2730_);
    lean_dec(v___x_2730_);
    v___x_2732_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2731_);
    return v___x_2732_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subSeconds___boxed(
    mut v_dt_2733_: *mut LeanObject,
    mut v_seconds_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_2733_, v_seconds_2734_);
    lean_dec(v_seconds_2734_);
    return v_res_2735_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMilliseconds(
    mut v_dt_2736_: *mut LeanObject,
    mut v_milliseconds_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    v___x_2738_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2736_);
    v_second_2739_ = lean_ctor_get(v___x_2738_, 0);
    lean_inc(v_second_2739_);
    v_nano_2740_ = lean_ctor_get(v___x_2738_, 1);
    lean_inc(v_nano_2740_);
    lean_dec_ref(v___x_2738_);
    v___x_2741_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
    );
    v___x_2742_ = lean_int_mul(v_milliseconds_2737_, v___x_2741_);
    v___x_2743_ = l_Std_Time_Duration_ofNanoseconds(v___x_2742_);
    lean_dec(v___x_2742_);
    v_second_2744_ = lean_ctor_get(v___x_2743_, 0);
    lean_inc(v_second_2744_);
    v_nano_2745_ = lean_ctor_get(v___x_2743_, 1);
    lean_inc(v_nano_2745_);
    lean_dec_ref(v___x_2743_);
    v___x_2746_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2747_ = lean_int_mul(v_second_2739_, v___x_2746_);
    lean_dec(v_second_2739_);
    v___x_2748_ = lean_int_add(v___x_2747_, v_nano_2740_);
    lean_dec(v_nano_2740_);
    lean_dec(v___x_2747_);
    v___x_2749_ = lean_int_mul(v_second_2744_, v___x_2746_);
    lean_dec(v_second_2744_);
    v___x_2750_ = lean_int_add(v___x_2749_, v_nano_2745_);
    lean_dec(v_nano_2745_);
    lean_dec(v___x_2749_);
    v___x_2751_ = lean_int_add(v___x_2748_, v___x_2750_);
    lean_dec(v___x_2750_);
    lean_dec(v___x_2748_);
    v___x_2752_ = l_Std_Time_Duration_ofNanoseconds(v___x_2751_);
    lean_dec(v___x_2751_);
    v___x_2753_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2752_);
    return v___x_2753_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMilliseconds___boxed(
    mut v_dt_2754_: *mut LeanObject,
    mut v_milliseconds_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2756_: *mut LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_2754_, v_milliseconds_2755_);
    lean_dec(v_milliseconds_2755_);
    return v_res_2756_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMilliseconds(
    mut v_dt_2757_: *mut LeanObject,
    mut v_milliseconds_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2757_);
    v_second_2760_ = lean_ctor_get(v___x_2759_, 0);
    lean_inc(v_second_2760_);
    v_nano_2761_ = lean_ctor_get(v___x_2759_, 1);
    lean_inc(v_nano_2761_);
    lean_dec_ref(v___x_2759_);
    v___x_2762_ = lean_int_neg(v_milliseconds_2758_);
    v___x_2763_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
    );
    v___x_2764_ = lean_int_mul(v___x_2762_, v___x_2763_);
    lean_dec(v___x_2762_);
    v___x_2765_ = l_Std_Time_Duration_ofNanoseconds(v___x_2764_);
    lean_dec(v___x_2764_);
    v_second_2766_ = lean_ctor_get(v___x_2765_, 0);
    lean_inc(v_second_2766_);
    v_nano_2767_ = lean_ctor_get(v___x_2765_, 1);
    lean_inc(v_nano_2767_);
    lean_dec_ref(v___x_2765_);
    v___x_2768_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2769_ = lean_int_mul(v_second_2760_, v___x_2768_);
    lean_dec(v_second_2760_);
    v___x_2770_ = lean_int_add(v___x_2769_, v_nano_2761_);
    lean_dec(v_nano_2761_);
    lean_dec(v___x_2769_);
    v___x_2771_ = lean_int_mul(v_second_2766_, v___x_2768_);
    lean_dec(v_second_2766_);
    v___x_2772_ = lean_int_add(v___x_2771_, v_nano_2767_);
    lean_dec(v_nano_2767_);
    lean_dec(v___x_2771_);
    v___x_2773_ = lean_int_add(v___x_2770_, v___x_2772_);
    lean_dec(v___x_2772_);
    lean_dec(v___x_2770_);
    v___x_2774_ = l_Std_Time_Duration_ofNanoseconds(v___x_2773_);
    lean_dec(v___x_2773_);
    v___x_2775_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2774_);
    return v___x_2775_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMilliseconds___boxed(
    mut v_dt_2776_: *mut LeanObject,
    mut v_milliseconds_2777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2778_: *mut LeanObject = core::ptr::null_mut();
    v_res_2778_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_2776_, v_milliseconds_2777_);
    lean_dec(v_milliseconds_2777_);
    return v_res_2778_;
}
pub unsafe fn l_Std_Time_PlainDateTime_year(mut v_dt_2779_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_2781_: *mut LeanObject = core::ptr::null_mut();
    v_date_2780_ = lean_ctor_get(v_dt_2779_, 0);
    v_year_2781_ = lean_ctor_get(v_date_2780_, 0);
    lean_inc(v_year_2781_);
    return v_year_2781_;
}
pub unsafe fn l_Std_Time_PlainDateTime_year___boxed(
    mut v_dt_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_res_2783_ = l_Std_Time_PlainDateTime_year(v_dt_2782_);
    lean_dec_ref(v_dt_2782_);
    return v_res_2783_;
}
pub unsafe fn l_Std_Time_PlainDateTime_month(mut v_dt_2784_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_2786_: *mut LeanObject = core::ptr::null_mut();
    v_date_2785_ = lean_ctor_get(v_dt_2784_, 0);
    v_month_2786_ = lean_ctor_get(v_date_2785_, 1);
    lean_inc(v_month_2786_);
    return v_month_2786_;
}
pub unsafe fn l_Std_Time_PlainDateTime_month___boxed(
    mut v_dt_2787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2788_: *mut LeanObject = core::ptr::null_mut();
    v_res_2788_ = l_Std_Time_PlainDateTime_month(v_dt_2787_);
    lean_dec_ref(v_dt_2787_);
    return v_res_2788_;
}
pub unsafe fn l_Std_Time_PlainDateTime_day(mut v_dt_2789_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2791_: *mut LeanObject = core::ptr::null_mut();
    v_date_2790_ = lean_ctor_get(v_dt_2789_, 0);
    v_day_2791_ = lean_ctor_get(v_date_2790_, 2);
    lean_inc(v_day_2791_);
    return v_day_2791_;
}
pub unsafe fn l_Std_Time_PlainDateTime_day___boxed(
    mut v_dt_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2793_: *mut LeanObject = core::ptr::null_mut();
    v_res_2793_ = l_Std_Time_PlainDateTime_day(v_dt_2792_);
    lean_dec_ref(v_dt_2792_);
    return v_res_2793_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekday(mut v_dt_2794_: *mut LeanObject) -> u8 {
    let mut v_date_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: u8 = 0;
    v_date_2795_ = lean_ctor_get(v_dt_2794_, 0);
    lean_inc_ref(v_date_2795_);
    lean_dec_ref(v_dt_2794_);
    v___x_2796_ = l_Std_Time_PlainDate_weekday(v_date_2795_);
    return v___x_2796_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekday___boxed(
    mut v_dt_2797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2798_: u8 = 0;
    let mut v_r_2799_: *mut LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Std_Time_PlainDateTime_weekday(v_dt_2797_);
    v_r_2799_ = lean_box((v_res_2798_) as usize);
    return v_r_2799_;
}
pub unsafe fn l_Std_Time_PlainDateTime_hour(mut v_dt_2800_: *mut LeanObject) -> *mut LeanObject {
    let mut v_time_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hour_2802_: *mut LeanObject = core::ptr::null_mut();
    v_time_2801_ = lean_ctor_get(v_dt_2800_, 1);
    v_hour_2802_ = lean_ctor_get(v_time_2801_, 0);
    lean_inc(v_hour_2802_);
    return v_hour_2802_;
}
pub unsafe fn l_Std_Time_PlainDateTime_hour___boxed(
    mut v_dt_2803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2804_: *mut LeanObject = core::ptr::null_mut();
    v_res_2804_ = l_Std_Time_PlainDateTime_hour(v_dt_2803_);
    lean_dec_ref(v_dt_2803_);
    return v_res_2804_;
}
pub unsafe fn l_Std_Time_PlainDateTime_minute(mut v_dt_2805_: *mut LeanObject) -> *mut LeanObject {
    let mut v_time_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_2807_: *mut LeanObject = core::ptr::null_mut();
    v_time_2806_ = lean_ctor_get(v_dt_2805_, 1);
    v_minute_2807_ = lean_ctor_get(v_time_2806_, 1);
    lean_inc(v_minute_2807_);
    return v_minute_2807_;
}
pub unsafe fn l_Std_Time_PlainDateTime_minute___boxed(
    mut v_dt_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2809_: *mut LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_Std_Time_PlainDateTime_minute(v_dt_2808_);
    lean_dec_ref(v_dt_2808_);
    return v_res_2809_;
}
pub unsafe fn l_Std_Time_PlainDateTime_millisecond(
    mut v_dt_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    v_time_2811_ = lean_ctor_get(v_dt_2810_, 1);
    v_nanosecond_2812_ = lean_ctor_get(v_time_2811_, 3);
    v___x_2813_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
    );
    v___x_2814_ = lean_int_ediv(v_nanosecond_2812_, v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn l_Std_Time_PlainDateTime_millisecond___boxed(
    mut v_dt_2815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2816_: *mut LeanObject = core::ptr::null_mut();
    v_res_2816_ = l_Std_Time_PlainDateTime_millisecond(v_dt_2815_);
    lean_dec_ref(v_dt_2815_);
    return v_res_2816_;
}
pub unsafe fn l_Std_Time_PlainDateTime_second(mut v_dt_2817_: *mut LeanObject) -> *mut LeanObject {
    let mut v_time_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2819_: *mut LeanObject = core::ptr::null_mut();
    v_time_2818_ = lean_ctor_get(v_dt_2817_, 1);
    v_second_2819_ = lean_ctor_get(v_time_2818_, 2);
    lean_inc(v_second_2819_);
    return v_second_2819_;
}
pub unsafe fn l_Std_Time_PlainDateTime_second___boxed(
    mut v_dt_2820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2821_: *mut LeanObject = core::ptr::null_mut();
    v_res_2821_ = l_Std_Time_PlainDateTime_second(v_dt_2820_);
    lean_dec_ref(v_dt_2820_);
    return v_res_2821_;
}
pub unsafe fn l_Std_Time_PlainDateTime_nanosecond(
    mut v_dt_2822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_time_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2824_: *mut LeanObject = core::ptr::null_mut();
    v_time_2823_ = lean_ctor_get(v_dt_2822_, 1);
    v_nanosecond_2824_ = lean_ctor_get(v_time_2823_, 3);
    lean_inc(v_nanosecond_2824_);
    return v_nanosecond_2824_;
}
pub unsafe fn l_Std_Time_PlainDateTime_nanosecond___boxed(
    mut v_dt_2825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2826_: *mut LeanObject = core::ptr::null_mut();
    v_res_2826_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_2825_);
    lean_dec_ref(v_dt_2825_);
    return v_res_2826_;
}
pub unsafe fn l_Std_Time_PlainDateTime_era(mut v_date_2827_: *mut LeanObject) -> u8 {
    let mut v_date_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: u8 = 0;
    v_date_2828_ = lean_ctor_get(v_date_2827_, 0);
    v_year_2829_ = lean_ctor_get(v_date_2828_, 0);
    v___x_2830_ = l_Std_Time_Year_Offset_era(v_year_2829_);
    return v___x_2830_;
}
pub unsafe fn l_Std_Time_PlainDateTime_era___boxed(
    mut v_date_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2832_: u8 = 0;
    let mut v_r_2833_: *mut LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Std_Time_PlainDateTime_era(v_date_2831_);
    lean_dec_ref(v_date_2831_);
    v_r_2833_ = lean_box((v_res_2832_) as usize);
    return v_r_2833_;
}
pub unsafe fn l_Std_Time_PlainDateTime_inLeapYear(mut v_date_2834_: *mut LeanObject) -> u8 {
    let mut v_date_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u8 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2835_ = lean_ctor_get(v_date_2834_, 0);
                v_year_2836_ = lean_ctor_get(v_date_2835_, 0);
                v___x_2837_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2838_ = lean_int_mod(v_year_2836_, v___x_2837_);
                v___x_2839_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2844_ = lean_int_dec_eq(v___x_2838_, v___x_2839_);
                lean_dec(v___x_2838_);
                if v___x_2844_ == 0 {
                    return v___x_2844_;
                } else {
                    v___x_2845_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2846_ = lean_int_mod(v_year_2836_, v___x_2845_);
                    v___x_2847_ = lean_int_dec_eq(v___x_2846_, v___x_2839_);
                    lean_dec(v___x_2846_);
                    if v___x_2847_ == 0 {
                        if v___x_2844_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_2844_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2841_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2842_ = lean_int_mod(v_year_2836_, v___x_2841_);
                v___x_2843_ = lean_int_dec_eq(v___x_2842_, v___x_2839_);
                lean_dec(v___x_2842_);
                return v___x_2843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_inLeapYear___boxed(
    mut v_date_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2849_: u8 = 0;
    let mut v_r_2850_: *mut LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_2848_);
    lean_dec_ref(v_date_2848_);
    v_r_2850_ = lean_box((v_res_2849_) as usize);
    return v_r_2850_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfYear(
    mut v_date_2851_: *mut LeanObject,
    mut v_firstDay_2852_: u8,
) -> *mut LeanObject {
    let mut v_date_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    v_date_2853_ = lean_ctor_get(v_date_2851_, 0);
    lean_inc_ref(v_date_2853_);
    lean_dec_ref(v_date_2851_);
    v___x_2854_ = l_Std_Time_PlainDate_weekOfYear(v_date_2853_, v_firstDay_2852_);
    return v___x_2854_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfYear___boxed(
    mut v_date_2855_: *mut LeanObject,
    mut v_firstDay_2856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2857_: u8 = 0;
    let mut v_res_2858_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2857_ = (lean_unbox(v_firstDay_2856_) as u8);
    v_res_2858_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_2855_, v_firstDay_boxed_2857_);
    return v_res_2858_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekYear(
    mut v_date_2859_: *mut LeanObject,
    mut v_firstDay_2860_: u8,
) -> *mut LeanObject {
    let mut v_date_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    v_date_2861_ = lean_ctor_get(v_date_2859_, 0);
    lean_inc_ref(v_date_2861_);
    lean_dec_ref(v_date_2859_);
    v___x_2862_ = l_Std_Time_PlainDate_weekYear(v_date_2861_, v_firstDay_2860_);
    return v___x_2862_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekYear___boxed(
    mut v_date_2863_: *mut LeanObject,
    mut v_firstDay_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2865_: u8 = 0;
    let mut v_res_2866_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2865_ = (lean_unbox(v_firstDay_2864_) as u8);
    v_res_2866_ = l_Std_Time_PlainDateTime_weekYear(v_date_2863_, v_firstDay_boxed_2865_);
    return v_res_2866_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfMonth(
    mut v_date_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    v_date_2868_ = lean_ctor_get(v_date_2867_, 0);
    v___x_2869_ = l_Std_Time_PlainDate_weekOfMonth(v_date_2868_);
    return v___x_2869_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfMonth___boxed(
    mut v_date_2870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2871_: *mut LeanObject = core::ptr::null_mut();
    v_res_2871_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_2870_);
    lean_dec_ref(v_date_2870_);
    return v_res_2871_;
}
pub unsafe fn l_Std_Time_PlainDateTime_alignedWeekOfMonth(
    mut v_date_2872_: *mut LeanObject,
    mut v_firstDay_2873_: u8,
) -> *mut LeanObject {
    let mut v_date_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    v_date_2874_ = lean_ctor_get(v_date_2872_, 0);
    lean_inc_ref(v_date_2874_);
    lean_dec_ref(v_date_2872_);
    v___x_2875_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2874_, v_firstDay_2873_);
    return v___x_2875_;
}
pub unsafe fn l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(
    mut v_date_2876_: *mut LeanObject,
    mut v_firstDay_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_2878_: u8 = 0;
    let mut v_res_2879_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2878_ = (lean_unbox(v_firstDay_2877_) as u8);
    v_res_2879_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_2876_, v_firstDay_boxed_2878_);
    return v_res_2879_;
}
pub unsafe fn l_Std_Time_PlainDateTime_dayOfYear(
    mut v_date_2880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v_year_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: u8 = 0;
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: u8 = 0;
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_unused_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2881_ = lean_ctor_get(v_date_2880_, 0);
                v_isSharedCheck_2905_ = (!lean_is_exclusive(v_date_2880_)) as u8;
                if v_isSharedCheck_2905_ == 0 {
                    v_unused_2906_ = lean_ctor_get(v_date_2880_, 1);
                    lean_dec(v_unused_2906_);
                    v___x_2883_ = v_date_2880_;
                    v_isShared_2884_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_2881_);
                    lean_dec(v_date_2880_);
                    v___x_2883_ = lean_box(0);
                    v_isShared_2884_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2885_ = lean_ctor_get(v_date_2881_, 0);
                lean_inc(v_year_2885_);
                v_month_2886_ = lean_ctor_get(v_date_2881_, 1);
                lean_inc(v_month_2886_);
                v_day_2887_ = lean_ctor_get(v_date_2881_, 2);
                lean_inc(v_day_2887_);
                lean_dec_ref(v_date_2881_);
                v___x_2894_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2895_ = lean_int_mod(v_year_2885_, v___x_2894_);
                v___x_2896_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2901_ = lean_int_dec_eq(v___x_2895_, v___x_2896_);
                lean_dec(v___x_2895_);
                if v___x_2901_ == 0 {
                    lean_dec(v_year_2885_);
                    v___y_2889_ = v___x_2901_;
                    state = 2;
                    continue;
                } else {
                    v___x_2902_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2903_ = lean_int_mod(v_year_2885_, v___x_2902_);
                    v___x_2904_ = lean_int_dec_eq(v___x_2903_, v___x_2896_);
                    lean_dec(v___x_2903_);
                    if v___x_2904_ == 0 {
                        if v___x_2901_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_year_2885_);
                            v___y_2889_ = v___x_2901_;
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2884_ == 0 {
                    lean_ctor_set(v___x_2883_, 1, v_day_2887_);
                    lean_ctor_set(v___x_2883_, 0, v_month_2886_);
                    v___x_2891_ = v___x_2883_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_month_2886_);
                    lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_day_2887_);
                    v___x_2891_ = v_reuseFailAlloc_2893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2892_ = l_Std_Time_ValidDate_dayOfYear(v___y_2889_, v___x_2891_);
                lean_dec_ref(v___x_2891_);
                return v___x_2892_;
            }
            4 => {
                v___x_2898_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2899_ = lean_int_mod(v_year_2885_, v___x_2898_);
                lean_dec(v_year_2885_);
                v___x_2900_ = lean_int_dec_eq(v___x_2899_, v___x_2896_);
                lean_dec(v___x_2899_);
                v___y_2889_ = v___x_2900_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_quarter(
    mut v_date_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v_date_2908_ = lean_ctor_get(v_date_2907_, 0);
    v___x_2909_ = l_Std_Time_PlainDate_quarter(v_date_2908_);
    return v___x_2909_;
}
pub unsafe fn l_Std_Time_PlainDateTime_quarter___boxed(
    mut v_date_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2911_: *mut LeanObject = core::ptr::null_mut();
    v_res_2911_ = l_Std_Time_PlainDateTime_quarter(v_date_2910_);
    lean_dec_ref(v_date_2910_);
    return v_res_2911_;
}
pub unsafe fn l_Std_Time_PlainDateTime_atTime(
    mut v_date_2912_: *mut LeanObject,
    mut v_time_2913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    v___x_2914_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2914_, 0, v_date_2912_);
    lean_ctor_set(v___x_2914_, 1, v_time_2913_);
    return v___x_2914_;
}
pub unsafe fn l_Std_Time_PlainDateTime_atDate(
    mut v_time_2915_: *mut LeanObject,
    mut v_date_2916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    v___x_2917_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2917_, 0, v_date_2916_);
    lean_ctor_set(v___x_2917_, 1, v_time_2915_);
    return v___x_2917_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instHAddDuration___lam__0(
    mut v_x_2946_: *mut LeanObject,
    mut v_y_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanos_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    v_second_2948_ = lean_ctor_get(v_y_2947_, 0);
    v_nano_2949_ = lean_ctor_get(v_y_2947_, 1);
    v___x_2950_ = l_Std_Time_PlainDateTime_toWallTime(v_x_2946_);
    v_second_2951_ = lean_ctor_get(v___x_2950_, 0);
    lean_inc(v_second_2951_);
    v_nano_2952_ = lean_ctor_get(v___x_2950_, 1);
    lean_inc(v_nano_2952_);
    lean_dec_ref(v___x_2950_);
    v___x_2953_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2954_ = lean_int_mul(v_second_2948_, v___x_2953_);
    v_nanos_2955_ = lean_int_add(v___x_2954_, v_nano_2949_);
    lean_dec(v___x_2954_);
    v___x_2956_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_2955_);
    lean_dec(v_nanos_2955_);
    v_second_2957_ = lean_ctor_get(v___x_2956_, 0);
    lean_inc(v_second_2957_);
    v_nano_2958_ = lean_ctor_get(v___x_2956_, 1);
    lean_inc(v_nano_2958_);
    lean_dec_ref(v___x_2956_);
    v___x_2959_ = lean_int_mul(v_second_2951_, v___x_2953_);
    lean_dec(v_second_2951_);
    v___x_2960_ = lean_int_add(v___x_2959_, v_nano_2952_);
    lean_dec(v_nano_2952_);
    lean_dec(v___x_2959_);
    v___x_2961_ = lean_int_mul(v_second_2957_, v___x_2953_);
    lean_dec(v_second_2957_);
    v___x_2962_ = lean_int_add(v___x_2961_, v_nano_2958_);
    lean_dec(v_nano_2958_);
    lean_dec(v___x_2961_);
    v___x_2963_ = lean_int_add(v___x_2960_, v___x_2962_);
    lean_dec(v___x_2962_);
    lean_dec(v___x_2960_);
    v___x_2964_ = l_Std_Time_Duration_ofNanoseconds(v___x_2963_);
    lean_dec(v___x_2963_);
    v___x_2965_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2964_);
    return v___x_2965_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(
    mut v_x_2966_: *mut LeanObject,
    mut v_y_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2968_: *mut LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_2966_, v_y_2967_);
    lean_dec_ref(v_y_2967_);
    return v_res_2968_;
}
pub unsafe fn l_Std_Time_PlainDate_atTime(
    mut v_date_2971_: *mut LeanObject,
    mut v_time_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    v___x_2973_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2973_, 0, v_date_2971_);
    lean_ctor_set(v___x_2973_, 1, v_time_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Std_Time_PlainTime_atDate(
    mut v_time_2974_: *mut LeanObject,
    mut v_date_2975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___x_2976_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2976_, 0, v_date_2975_);
    lean_ctor_set(v___x_2976_, 1, v_time_2974_);
    return v___x_2976_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_instInhabitedPlainDateTime_default =
        _init_l_Std_Time_instInhabitedPlainDateTime_default();
    lean_mark_persistent(l_Std_Time_instInhabitedPlainDateTime_default);
    l_Std_Time_instInhabitedPlainDateTime = _init_l_Std_Time_instInhabitedPlainDateTime();
    lean_mark_persistent(l_Std_Time_instInhabitedPlainDateTime);
    l_Std_Time_instOrdPlainDateTime = _init_l_Std_Time_instOrdPlainDateTime();
    lean_mark_persistent(l_Std_Time_instOrdPlainDateTime);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime_PlainDateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_DateTime_PlainDateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_DateTime_WallTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_DateTime_PlainDateTime(builtin);
}
