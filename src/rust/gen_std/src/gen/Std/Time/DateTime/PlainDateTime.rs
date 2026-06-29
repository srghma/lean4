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
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__18_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__25_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__26_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__27_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__28_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__29_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__30_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__31_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__33_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__34_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__35_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__36_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__37_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__38_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__39_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instInhabitedPlainDateTime_default___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainDateTime_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instInhabitedPlainDateTime: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value:
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value:
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
    m_data: [100, 97, 116, 101, 0],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value:
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value:
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value:
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
    m_data: [116, 105, 109, 101, 0],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value:
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
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16_value:
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
        core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instReprPlainDateTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instReprPlainDateTime_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instReprPlainDateTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_instReprPlainDateTime: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instReprPlainDateTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDateTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDateTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDateTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDateTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdPlainDateTime___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdPlainDateTime___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdPlainDateTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdPlainDateTime___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instOrdPlainDateTime___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdPlainDateTime___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instOrdPlainDateTime___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdPlainDateTime___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_instOrdPlainDateTime___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdPlainDateTime___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_instOrdPlainDateTime: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_toWallTime___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_toWallTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_toWallTime___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_toWallTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__18_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__22_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__23_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__25_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__28_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__29_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__31_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__32_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_ofWallTime___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_withMilliseconds___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addWeeks___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_addWeeks___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_addYearsRollOver___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_addHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_PlainDateTime_addMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_PlainDateTime_addMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_addDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_subDays___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubOffset___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_addWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_subWeeks___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_addHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_subHours___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_addMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_subMinutes___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_addMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_subMilliseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_addSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_subSeconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_addNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_subNanoseconds___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHSubOffset__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHSubOffset__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value:
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
    m_fun: l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_PlainDateTime_instHAddDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Std_Time_PlainDateTime_instHAddDuration: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_PlainDateTime_instHAddDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Nat_cast___at___00Std_Time_instInhabitedPlainDateTime_default_spec__0(
    mut v_a_1489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1490_ = lean_nat_to_int(v_a_1489_);
    return v___x_1490_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1492_ = lean_nat_to_int(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1494_ = lean_nat_to_int(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1496_ = lean_nat_to_int(v___x_1495_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__2_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__2,
    );
    v___x_1498_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1499_ = lean_int_add(v___x_1498_, v___x_1497_);
    return v___x_1499_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1501_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__3_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__3,
    );
    v___x_1502_ = lean_int_sub(v___x_1501_, v___x_1500_);
    return v___x_1502_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1503_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1504_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__4_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__4,
    );
    v_range_1505_ = lean_int_add(v___x_1504_, v___x_1503_);
    return v_range_1505_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1506_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1507_ = lean_int_sub(v___x_1506_, v___x_1506_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1508_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5,
    );
    v___x_1509_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6,
    );
    v___x_1510_ = lean_int_emod(v___x_1509_, v_range_1508_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1511_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5,
    );
    v___x_1512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__7_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__7,
    );
    v___x_1513_ = lean_int_add(v___x_1512_, v_range_1511_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1514_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__5_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__5,
    );
    v___x_1515_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__8_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__8,
    );
    v___x_1516_ = lean_int_emod(v___x_1515_, v_range_1514_);
    return v___x_1516_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1518_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__9),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__9_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__9,
    );
    v___x_1519_ = lean_int_add(v___x_1518_, v___x_1517_);
    return v___x_1519_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1520_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_1521_ = lean_nat_to_int(v___x_1520_);
    return v___x_1521_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1523_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1524_ = lean_int_add(v___x_1523_, v___x_1522_);
    return v___x_1524_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1526_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__12),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__12_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__12,
    );
    v___x_1527_ = lean_int_sub(v___x_1526_, v___x_1525_);
    return v___x_1527_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1529_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__13_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__13,
    );
    v_range_1530_ = lean_int_add(v___x_1529_, v___x_1528_);
    return v_range_1530_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1531_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14,
    );
    v___x_1532_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__6_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__6,
    );
    v___x_1533_ = lean_int_emod(v___x_1532_, v_range_1531_);
    return v___x_1533_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1534_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14,
    );
    v___x_1535_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__15_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__15,
    );
    v___x_1536_ = lean_int_add(v___x_1535_, v_range_1534_);
    return v___x_1536_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1537_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__14_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__14,
    );
    v___x_1538_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__16_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__16,
    );
    v___x_1539_ = lean_int_emod(v___x_1538_, v_range_1537_);
    return v___x_1539_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1541_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__17_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__17,
    );
    v___x_1542_ = lean_int_add(v___x_1541_, v___x_1540_);
    return v___x_1542_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1543_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__18_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__18,
    );
    v___x_1544_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__10_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__10,
    );
    v___x_1545_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1546_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1546_, 0, v___x_1545_);
    crate::leanh::lean_ctor_set(v___x_1546_, 1, v___x_1544_);
    crate::leanh::lean_ctor_set(v___x_1546_, 2, v___x_1543_);
    return v___x_1546_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = crate::leanh::lean_unsigned_to_nat(23);
    v___x_1548_ = lean_nat_to_int(v___x_1547_);
    return v___x_1548_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__20_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__20,
    );
    v___x_1550_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1551_ = lean_int_add(v___x_1550_, v___x_1549_);
    return v___x_1551_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1553_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__21_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__21,
    );
    v___x_1554_ = lean_int_sub(v___x_1553_, v___x_1552_);
    return v___x_1554_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1556_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__22_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__22,
    );
    v_range_1557_ = lean_int_add(v___x_1556_, v___x_1555_);
    return v_range_1557_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1559_ = lean_int_sub(v___x_1558_, v___x_1558_);
    return v___x_1559_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1560_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23,
    );
    v___x_1561_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24,
    );
    v___x_1562_ = lean_int_emod(v___x_1561_, v_range_1560_);
    return v___x_1562_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1563_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23,
    );
    v___x_1564_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__25_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__25,
    );
    v___x_1565_ = lean_int_add(v___x_1564_, v_range_1563_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1566_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__23_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__23,
    );
    v___x_1567_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__26_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__26,
    );
    v___x_1568_ = lean_int_emod(v___x_1567_, v_range_1566_);
    return v___x_1568_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1569_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1570_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__27),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__27_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__27,
    );
    v___x_1571_ = lean_int_add(v___x_1570_, v___x_1569_);
    return v___x_1571_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1572_ = crate::leanh::lean_unsigned_to_nat(59);
    v___x_1573_ = lean_nat_to_int(v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1574_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__29),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__29_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__29,
    );
    v___x_1575_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1576_ = lean_int_add(v___x_1575_, v___x_1574_);
    return v___x_1576_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1577_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1578_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__30),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__30_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__30,
    );
    v___x_1579_ = lean_int_sub(v___x_1578_, v___x_1577_);
    return v___x_1579_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1581_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__31),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__31_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__31,
    );
    v_range_1582_ = lean_int_add(v___x_1581_, v___x_1580_);
    return v_range_1582_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1583_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32,
    );
    v___x_1584_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__24_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__24,
    );
    v___x_1585_ = lean_int_emod(v___x_1584_, v_range_1583_);
    return v___x_1585_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1586_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32,
    );
    v___x_1587_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__33),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__33_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__33,
    );
    v___x_1588_ = lean_int_add(v___x_1587_, v_range_1586_);
    return v___x_1588_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v_range_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_range_1589_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__32_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__32,
    );
    v___x_1590_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__34),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__34_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__34,
    );
    v___x_1591_ = lean_int_emod(v___x_1590_, v_range_1589_);
    return v___x_1591_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__36()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1593_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__35),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__35_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__35,
    );
    v___x_1594_ = lean_int_add(v___x_1593_, v___x_1592_);
    return v___x_1594_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1596_ = 1;
    v___x_1597_ = l_Std_Time_Second_instOfNatOrdinal(v___x_1596_, v___x_1595_);
    return v___x_1597_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__38()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
    );
    v___x_1599_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__37),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__37_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__37,
    );
    v___x_1600_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__36),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__36_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__36,
    );
    v___x_1601_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__28),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__28_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__28,
    );
    v___x_1602_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1602_, 0, v___x_1601_);
    crate::leanh::lean_ctor_set(v___x_1602_, 1, v___x_1600_);
    crate::leanh::lean_ctor_set(v___x_1602_, 2, v___x_1599_);
    crate::leanh::lean_ctor_set(v___x_1602_, 3, v___x_1598_);
    return v___x_1602_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__39()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__38),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__38_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__38,
    );
    v___x_1604_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__19_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__19,
    );
    v___x_1605_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1605_, 0, v___x_1604_);
    crate::leanh::lean_ctor_set(v___x_1605_, 1, v___x_1603_);
    return v___x_1605_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime_default() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__39),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__39_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__39,
    );
    return v___x_1606_;
}
pub unsafe fn _init_l_Std_Time_instInhabitedPlainDateTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = l_Std_Time_instInhabitedPlainDateTime_default;
    return v___x_1607_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDateTime_decEq(
    mut v_x_1608_: *mut crate::leanh::LeanObject,
    mut v_x_1609_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    v_date_1610_ = crate::leanh::lean_ctor_get(v_x_1608_, 0);
    v_time_1611_ = crate::leanh::lean_ctor_get(v_x_1608_, 1);
    v_date_1612_ = crate::leanh::lean_ctor_get(v_x_1609_, 0);
    v_time_1613_ = crate::leanh::lean_ctor_get(v_x_1609_, 1);
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
    mut v_x_1616_: *mut crate::leanh::LeanObject,
    mut v_x_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1618_: u8 = 0;
    let mut v_r_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1618_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_1616_, v_x_1617_);
    crate::leanh::lean_dec_ref(v_x_1617_);
    crate::leanh::lean_dec_ref(v_x_1616_);
    v_r_1619_ = crate::leanh::lean_box((v_res_1618_) as usize);
    return v_r_1619_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDateTime(
    mut v_x_1620_: *mut crate::leanh::LeanObject,
    mut v_x_1621_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1622_: u8 = 0;
    v___x_1622_ = l_Std_Time_instDecidableEqPlainDateTime_decEq(v_x_1620_, v_x_1621_);
    return v___x_1622_;
}
pub unsafe fn l_Std_Time_instDecidableEqPlainDateTime___boxed(
    mut v_x_1623_: *mut crate::leanh::LeanObject,
    mut v_x_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: u8 = 0;
    let mut v_r_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l_Std_Time_instDecidableEqPlainDateTime(v_x_1623_, v_x_1624_);
    crate::leanh::lean_dec_ref(v_x_1624_);
    crate::leanh::lean_dec_ref(v_x_1623_);
    v_r_1626_ = crate::leanh::lean_box((v_res_1625_) as usize);
    return v_r_1626_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_1641_ = lean_nat_to_int(v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1649_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__0;
    v___x_1650_ = lean_string_length(v___x_1649_);
    return v___x_1650_;
}
pub unsafe fn _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13_once),
        _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__13,
    );
    v___x_1652_ = lean_nat_to_int(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn l_Std_Time_instReprPlainDateTime_repr___redArg(
    mut v_x_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: u8 = 0;
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_1658_ = crate::leanh::lean_ctor_get(v_x_1657_, 0);
                v_time_1659_ = crate::leanh::lean_ctor_get(v_x_1657_, 1);
                v_isSharedCheck_1691_ = (!crate::leanh::lean_is_exclusive(v_x_1657_)) as u8;
                if v_isSharedCheck_1691_ == 0 {
                    v___x_1661_ = v_x_1657_;
                    v_isShared_1662_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_1659_);
                    crate::leanh::lean_inc(v_date_1658_);
                    crate::leanh::lean_dec(v_x_1657_);
                    v___x_1661_ = crate::leanh::lean_box(0);
                    v_isShared_1662_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1663_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__5;
                v___x_1664_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__6;
                v___x_1665_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7_once
                    ),
                    _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__7,
                );
                v___x_1666_ = l_Std_Time_instReprPlainDate_repr___redArg(v_date_1658_);
                crate::leanh::lean_dec_ref(v_date_1658_);
                if v_isShared_1662_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1661_, 4);
                    crate::leanh::lean_ctor_set(v___x_1661_, 1, v___x_1666_);
                    crate::leanh::lean_ctor_set(v___x_1661_, 0, v___x_1665_);
                    v___x_1668_ = v___x_1661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 1, v___x_1666_);
                    v___x_1668_ = v_reuseFailAlloc_1690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1669_ = 0;
                v___x_1670_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1668_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1670_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1669_,
                );
                v___x_1671_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1671_, 0, v___x_1664_);
                crate::leanh::lean_ctor_set(v___x_1671_, 1, v___x_1670_);
                v___x_1672_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__9;
                v___x_1673_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1673_, 0, v___x_1671_);
                crate::leanh::lean_ctor_set(v___x_1673_, 1, v___x_1672_);
                v___x_1674_ = crate::leanh::lean_box(1);
                v___x_1675_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1675_, 0, v___x_1673_);
                crate::leanh::lean_ctor_set(v___x_1675_, 1, v___x_1674_);
                v___x_1676_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__11;
                v___x_1677_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1675_);
                crate::leanh::lean_ctor_set(v___x_1677_, 1, v___x_1676_);
                v___x_1678_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                crate::leanh::lean_ctor_set(v___x_1678_, 1, v___x_1663_);
                v___x_1679_ = l_Std_Time_instReprPlainTime_repr___redArg(v_time_1659_);
                crate::leanh::lean_dec_ref(v_time_1659_);
                v___x_1680_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1680_, 0, v___x_1665_);
                crate::leanh::lean_ctor_set(v___x_1680_, 1, v___x_1679_);
                v___x_1681_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1680_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1681_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1669_,
                );
                v___x_1682_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1678_);
                crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                v___x_1683_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14_once
                    ),
                    _init_l_Std_Time_instReprPlainDateTime_repr___redArg___closed__14,
                );
                v___x_1684_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__15;
                v___x_1685_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1685_, 0, v___x_1684_);
                crate::leanh::lean_ctor_set(v___x_1685_, 1, v___x_1682_);
                v___x_1686_ = l_Std_Time_instReprPlainDateTime_repr___redArg___closed__16;
                v___x_1687_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1687_, 0, v___x_1685_);
                crate::leanh::lean_ctor_set(v___x_1687_, 1, v___x_1686_);
                v___x_1688_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1688_, 0, v___x_1683_);
                crate::leanh::lean_ctor_set(v___x_1688_, 1, v___x_1687_);
                v___x_1689_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1689_, 0, v___x_1688_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1689_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1669_,
                );
                return v___x_1689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_instReprPlainDateTime_repr(
    mut v_x_1692_: *mut crate::leanh::LeanObject,
    mut v_prec_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_Std_Time_instReprPlainDateTime_repr___redArg(v_x_1692_);
    return v___x_1694_;
}
pub unsafe fn l_Std_Time_instReprPlainDateTime_repr___boxed(
    mut v_x_1695_: *mut crate::leanh::LeanObject,
    mut v_prec_1696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1697_ = l_Std_Time_instReprPlainDateTime_repr(v_x_1695_, v_prec_1696_);
    crate::leanh::lean_dec(v_prec_1696_);
    return v_res_1697_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__0(
    mut v_x_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_1701_ = crate::leanh::lean_ctor_get(v_x_1700_, 0);
    crate::leanh::lean_inc_ref(v_date_1701_);
    return v_date_1701_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__0___boxed(
    mut v_x_1702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_Std_Time_instOrdPlainDateTime___lam__0(v_x_1702_);
    crate::leanh::lean_dec_ref(v_x_1702_);
    return v_res_1703_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__1(
    mut v_x_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_time_1705_ = crate::leanh::lean_ctor_get(v_x_1704_, 1);
    crate::leanh::lean_inc_ref(v_time_1705_);
    return v_time_1705_;
}
pub unsafe fn l_Std_Time_instOrdPlainDateTime___lam__1___boxed(
    mut v_x_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Std_Time_instOrdPlainDateTime___lam__1(v_x_1706_);
    crate::leanh::lean_dec_ref(v_x_1706_);
    return v_res_1707_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___f_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1710_ = l_Std_Time_instOrdPlainDateTime___closed__0;
    v___x_1711_ = l_Std_Time_instOrdPlainDate;
    v___x_1712_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1712_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1712_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1712_, 2, v___x_1711_);
    crate::leanh::lean_closure_set(v___x_1712_, 3, v___f_1710_);
    return v___x_1712_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___f_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1713_ = l_Std_Time_instOrdPlainDateTime___closed__1;
    v___x_1714_ = l_Std_Time_instOrdPlainTime;
    v___x_1715_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1715_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1715_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1715_, 2, v___x_1714_);
    crate::leanh::lean_closure_set(v___x_1715_, 3, v___f_1713_);
    return v___x_1715_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__3_once),
        _init_l_Std_Time_instOrdPlainDateTime___closed__3,
    );
    v___x_1717_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__2_once),
        _init_l_Std_Time_instOrdPlainDateTime___closed__2,
    );
    v___x_1718_ =
        crate::leanh::lean_alloc_closure(l_compareLex___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1718_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1718_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1718_, 2, v___x_1717_);
    crate::leanh::lean_closure_set(v___x_1718_, 3, v___x_1716_);
    return v___x_1718_;
}
pub unsafe fn _init_l_Std_Time_instOrdPlainDateTime() -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdPlainDateTime___closed__4_once),
        _init_l_Std_Time_instOrdPlainDateTime___closed__4,
    );
    return v___x_1719_;
}
pub unsafe fn l_Int_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__1(
    mut v_a_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Rat_ofInt(v_a_1720_);
    return v___x_1721_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_toWallTime___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1722_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_1723_ = lean_nat_to_int(v___x_1722_);
    return v___x_1723_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_toWallTime___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_1725_ = lean_nat_to_int(v___x_1724_);
    return v___x_1725_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toWallTime(
    mut v_dt_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_days_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_time_1727_ = crate::leanh::lean_ctor_get(v_dt_1726_, 1);
    crate::leanh::lean_inc_ref(v_time_1727_);
    v_date_1728_ = crate::leanh::lean_ctor_get(v_dt_1726_, 0);
    crate::leanh::lean_inc_ref(v_date_1728_);
    crate::leanh::lean_dec_ref(v_dt_1726_);
    v_nanosecond_1729_ = crate::leanh::lean_ctor_get(v_time_1727_, 3);
    crate::leanh::lean_inc(v_nanosecond_1729_);
    v_days_1730_ = l_Std_Time_PlainDate_toEpochDay(v_date_1728_);
    v___x_1731_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__0,
    );
    v___x_1732_ = lean_int_mul(v_days_1730_, v___x_1731_);
    crate::leanh::lean_dec(v_days_1730_);
    v___x_1733_ = l_Std_Time_PlainTime_toSeconds(v_time_1727_);
    crate::leanh::lean_dec_ref(v_time_1727_);
    v___x_1734_ = lean_int_add(v___x_1732_, v___x_1733_);
    crate::leanh::lean_dec(v___x_1733_);
    crate::leanh::lean_dec(v___x_1732_);
    v___x_1735_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_1736_ = lean_int_mul(v___x_1734_, v___x_1735_);
    crate::leanh::lean_dec(v___x_1734_);
    v_nanos_1737_ = lean_int_add(v___x_1736_, v_nanosecond_1729_);
    crate::leanh::lean_dec(v_nanosecond_1729_);
    crate::leanh::lean_dec(v___x_1736_);
    v___x_1738_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_1737_);
    crate::leanh::lean_dec(v_nanos_1737_);
    return v___x_1738_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_PlainDateTime_toWallTime_spec__0(
    mut v_a_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = lean_nat_to_int(v_a_1739_);
    v___x_1741_ = l_Rat_ofInt(v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_1743_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1744_ = lean_nat_mod(v___x_1743_, v___x_1742_);
    return v___x_1744_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(
    mut v_as_x27_1745_: *mut crate::leanh::LeanObject,
    mut v_b_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1753_: u8 = 0;
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_1745_) == 0 {
                    return v_b_1746_;
                } else {
                    v_head_1747_ = crate::leanh::lean_ctor_get(v_as_x27_1745_, 0);
                    v_tail_1748_ = crate::leanh::lean_ctor_get(v_as_x27_1745_, 1);
                    v_fst_1749_ = crate::leanh::lean_ctor_get(v_b_1746_, 0);
                    v_snd_1750_ = crate::leanh::lean_ctor_get(v_b_1746_, 1);
                    v_isSharedCheck_1766_ = (!crate::leanh::lean_is_exclusive(v_b_1746_)) as u8;
                    if v_isSharedCheck_1766_ == 0 {
                        v___x_1752_ = v_b_1746_;
                        v_isShared_1753_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1750_);
                        crate::leanh::lean_inc(v_fst_1749_);
                        crate::leanh::lean_dec(v_b_1746_);
                        v___x_1752_ = crate::leanh::lean_box(0);
                        v_isShared_1753_ = v_isSharedCheck_1766_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1754_ = crate::leanh::lean_unsigned_to_nat(13);
                v___x_1755_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0_once), _init_l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg___closed__0);
                v___x_1756_ = l_Fin_add(v___x_1754_, v_snd_1750_, v___x_1755_);
                crate::leanh::lean_dec(v_snd_1750_);
                v___x_1757_ = lean_int_dec_lt(v_fst_1749_, v_head_1747_);
                if v___x_1757_ == 0 {
                    v___x_1758_ = lean_int_sub(v_fst_1749_, v_head_1747_);
                    crate::leanh::lean_dec(v_fst_1749_);
                    if v_isShared_1753_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1752_, 1, v___x_1756_);
                        crate::leanh::lean_ctor_set(v___x_1752_, 0, v___x_1758_);
                        v___x_1760_ = v___x_1752_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1762_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1758_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1756_);
                        v___x_1760_ = v_reuseFailAlloc_1762_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_1753_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1752_, 1, v___x_1756_);
                        v___x_1764_ = v___x_1752_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_fst_1749_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1765_, 1, v___x_1756_);
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
    mut v_as_x27_1767_: *mut crate::leanh::LeanObject,
    mut v_b_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(
        v_as_x27_1767_,
        v_b_1768_,
    );
    crate::leanh::lean_dec(v_as_x27_1767_);
    return v_res_1769_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = crate::leanh::lean_unsigned_to_nat(11017);
    v___x_1771_ = lean_nat_to_int(v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1772_ = crate::leanh::lean_unsigned_to_nat(365);
    v___x_1773_ = lean_nat_to_int(v___x_1772_);
    return v___x_1773_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = crate::leanh::lean_unsigned_to_nat(400);
    v___x_1775_ = lean_nat_to_int(v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1776_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
    );
    v___x_1777_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
    );
    v___x_1778_ = lean_int_mul(v___x_1777_, v___x_1776_);
    return v___x_1778_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = crate::leanh::lean_unsigned_to_nat(97);
    v___x_1780_ = lean_nat_to_int(v___x_1779_);
    return v___x_1780_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysPer400Y_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__4),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__4_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__4,
    );
    v___x_1782_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__3),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__3_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__3,
    );
    v_daysPer400Y_1783_ = lean_int_add(v___x_1782_, v___x_1781_);
    return v_daysPer400Y_1783_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = crate::leanh::lean_unsigned_to_nat(100);
    v___x_1785_ = lean_nat_to_int(v___x_1784_);
    return v___x_1785_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
    );
    v___x_1787_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
    );
    v___x_1788_ = lean_int_mul(v___x_1787_, v___x_1786_);
    return v___x_1788_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1789_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_1790_ = lean_nat_to_int(v___x_1789_);
    return v___x_1790_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysPer100Y_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__8),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__8_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__8,
    );
    v___x_1792_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__7),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__7_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__7,
    );
    v_daysPer100Y_1793_ = lean_int_add(v___x_1792_, v___x_1791_);
    return v_daysPer100Y_1793_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1794_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1795_ = lean_nat_to_int(v___x_1794_);
    return v___x_1795_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
    );
    v___x_1797_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
    );
    v___x_1798_ = lean_int_mul(v___x_1797_, v___x_1796_);
    return v___x_1798_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysPer4Y_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1800_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__11_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__11,
    );
    v_daysPer4Y_1801_ = lean_int_add(v___x_1800_, v___x_1799_);
    return v_daysPer4Y_1801_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1802_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_1803_ = lean_nat_to_int(v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1804_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_1805_ = lean_nat_to_int(v___x_1804_);
    return v___x_1805_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_1807_ = lean_nat_to_int(v___x_1806_);
    return v___x_1807_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1808_ = crate::leanh::lean_unsigned_to_nat(29);
    v___x_1809_ = lean_nat_to_int(v___x_1808_);
    return v___x_1809_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1810_ = crate::leanh::lean_box(0);
    v___x_1811_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__16),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__16_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__16,
    );
    v___x_1812_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1812_, 0, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1812_, 1, v___x_1810_);
    return v___x_1812_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__17),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__17_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__17,
    );
    v___x_1814_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1815_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1815_, 0, v___x_1814_);
    crate::leanh::lean_ctor_set(v___x_1815_, 1, v___x_1813_);
    return v___x_1815_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1816_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__18),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__18_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__18,
    );
    v___x_1817_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1818_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1818_, 0, v___x_1817_);
    crate::leanh::lean_ctor_set(v___x_1818_, 1, v___x_1816_);
    return v___x_1818_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1819_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__19),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__19_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__19,
    );
    v___x_1820_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1821_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1821_, 0, v___x_1820_);
    crate::leanh::lean_ctor_set(v___x_1821_, 1, v___x_1819_);
    return v___x_1821_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1822_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__20),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__20_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__20,
    );
    v___x_1823_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1824_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1824_, 0, v___x_1823_);
    crate::leanh::lean_ctor_set(v___x_1824_, 1, v___x_1822_);
    return v___x_1824_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__21),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__21_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__21,
    );
    v___x_1826_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1827_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1827_, 0, v___x_1826_);
    crate::leanh::lean_ctor_set(v___x_1827_, 1, v___x_1825_);
    return v___x_1827_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1828_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__22),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__22_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__22,
    );
    v___x_1829_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1830_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1829_);
    crate::leanh::lean_ctor_set(v___x_1830_, 1, v___x_1828_);
    return v___x_1830_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__23),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__23_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__23,
    );
    v___x_1832_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1833_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1833_, 0, v___x_1832_);
    crate::leanh::lean_ctor_set(v___x_1833_, 1, v___x_1831_);
    return v___x_1833_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__24),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__24_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__24,
    );
    v___x_1835_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1836_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1836_, 0, v___x_1835_);
    crate::leanh::lean_ctor_set(v___x_1836_, 1, v___x_1834_);
    return v___x_1836_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1837_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__25),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__25_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__25,
    );
    v___x_1838_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v___x_1839_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1839_, 0, v___x_1838_);
    crate::leanh::lean_ctor_set(v___x_1839_, 1, v___x_1837_);
    return v___x_1839_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__26),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__26_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__26,
    );
    v___x_1841_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__11_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__11,
    );
    v___x_1842_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1842_, 0, v___x_1841_);
    crate::leanh::lean_ctor_set(v___x_1842_, 1, v___x_1840_);
    return v___x_1842_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_months_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__27),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__27_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__27,
    );
    v___x_1844_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__15_once),
        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__15,
    );
    v_months_1845_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_months_1845_, 0, v___x_1844_);
    crate::leanh::lean_ctor_set(v_months_1845_, 1, v___x_1843_);
    return v_months_1845_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mon_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1846_ = crate::leanh::lean_unsigned_to_nat(13);
    v___x_1847_ = crate::leanh::lean_unsigned_to_nat(0);
    v_mon_1848_ = lean_nat_mod(v___x_1847_, v___x_1846_);
    return v_mon_1848_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = crate::leanh::lean_unsigned_to_nat(2000);
    v___x_1850_ = lean_nat_to_int(v___x_1849_);
    return v___x_1850_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__31()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1851_ = crate::leanh::lean_unsigned_to_nat(25);
    v___x_1852_ = lean_nat_to_int(v___x_1851_);
    return v___x_1852_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_ofWallTime___closed__32()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once),
        _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
    );
    v___x_1854_ = lean_int_neg(v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofWallTime(
    mut v_stamp_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1872_: u8 = 0;
    let mut v_max_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: u8 = 0;
    let mut v_daysPer400Y_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysPer100Y_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: u8 = 0;
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysPer4Y_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hmon_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: u8 = 0;
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remYears_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remDays_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_months_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mon_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quadrennialCycles_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remDays_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remYears_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: u8 = 0;
    let mut v_remYears_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_centenialCycles_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remDays_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quadrennialCycles_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: u8 = 0;
    let mut v_quadrennialCycles_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quadracentennialCycles_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remDays_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_centenialCycles_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: u8 = 0;
    let mut v_centenialCycles_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quadracentennialCycles_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_remDays_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: u8 = 0;
    let mut v_remDays_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quadracentennialCycles_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_boundedDaysSinceEpoch_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawDays_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rawDays_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_secs_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_1877_ = crate::leanh::lean_ctor_get(v_stamp_1855_, 0);
                v_nano_1878_ = crate::leanh::lean_ctor_get(v_stamp_1855_, 1);
                v_isSharedCheck_2026_ = (!crate::leanh::lean_is_exclusive(v_stamp_1855_)) as u8;
                if v_isSharedCheck_2026_ == 0 {
                    v___x_1880_ = v_stamp_1855_;
                    v_isShared_1881_ = v_isSharedCheck_2026_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_1878_);
                    crate::leanh::lean_inc(v_second_1877_);
                    crate::leanh::lean_dec(v_stamp_1855_);
                    v___x_1880_ = crate::leanh::lean_box(0);
                    v_isShared_1881_ = v_isSharedCheck_2026_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_1862_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1862_, 0, v___y_1859_);
                crate::leanh::lean_ctor_set(v___x_1862_, 1, v___y_1857_);
                crate::leanh::lean_ctor_set(v___x_1862_, 2, v___y_1860_);
                crate::leanh::lean_ctor_set(v___x_1862_, 3, v___y_1858_);
                v___x_1863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1863_, 0, v___y_1861_);
                crate::leanh::lean_ctor_set(v___x_1863_, 1, v___x_1862_);
                return v___x_1863_;
            }
            2 => {
                v_max_1873_ = l_Std_Time_Month_Ordinal_days(v___y_1872_, v___y_1868_);
                v___x_1874_ = lean_int_dec_lt(v_max_1873_, v___y_1870_);
                if v___x_1874_ == 0 {
                    crate::leanh::lean_dec(v_max_1873_);
                    v___x_1875_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1875_, 0, v___y_1869_);
                    crate::leanh::lean_ctor_set(v___x_1875_, 1, v___y_1868_);
                    crate::leanh::lean_ctor_set(v___x_1875_, 2, v___y_1870_);
                    v___y_1857_ = v___y_1865_;
                    v___y_1858_ = v___y_1867_;
                    v___y_1859_ = v___y_1866_;
                    v___y_1860_ = v___y_1871_;
                    v___y_1861_ = v___x_1875_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1870_);
                    v___x_1876_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1876_, 0, v___y_1869_);
                    crate::leanh::lean_ctor_set(v___x_1876_, 1, v___y_1868_);
                    crate::leanh::lean_ctor_set(v___x_1876_, 2, v_max_1873_);
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
                v___x_1882_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__0,
                );
                v___x_1883_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__1,
                );
                v___x_1884_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v_daysPer400Y_1896_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__5),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__5_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__5,
                );
                v___x_1897_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                );
                v_daysPer100Y_1898_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__9),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__9_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__9,
                );
                v___x_1899_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_1914_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1915_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__1_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__1,
                );
                v_daysPer4Y_1916_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__12),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__12_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__12,
                );
                v___x_1917_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
                    _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
                );
                v___x_1918_ = lean_int_mul(v_second_1877_, v___x_1917_);
                crate::leanh::lean_dec(v_second_1877_);
                v___x_1919_ = lean_int_add(v___x_1918_, v_nano_1878_);
                crate::leanh::lean_dec(v_nano_1878_);
                crate::leanh::lean_dec(v___x_1918_);
                v_secs_2021_ = lean_int_div(v___x_1919_, v___x_1917_);
                v___x_2022_ = lean_int_mod(v___x_1919_, v___x_1917_);
                v___x_2023_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2024_ = lean_int_dec_lt(v___x_2022_, v___x_2023_);
                crate::leanh::lean_dec(v___x_2022_);
                if v___x_2024_ == 0 {
                    v_snd_2012_ = v_secs_2021_;
                    state = 13;
                    continue;
                } else {
                    v___x_2025_ = lean_int_sub(v_secs_2021_, v___x_1915_);
                    crate::leanh::lean_dec(v_secs_2021_);
                    v_snd_2012_ = v___x_2025_;
                    state = 13;
                    continue;
                }
            }
            4 => {
                v___x_1894_ = lean_int_mod(v___y_1891_, v___x_1884_);
                v___x_1895_ = lean_int_dec_eq(v___x_1894_, v___y_1887_);
                crate::leanh::lean_dec(v___y_1887_);
                crate::leanh::lean_dec(v___x_1894_);
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
                crate::leanh::lean_dec(v___x_1909_);
                if v___x_1911_ == 0 {
                    crate::leanh::lean_dec(v___x_1910_);
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
                    crate::leanh::lean_dec(v___x_1912_);
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
                            crate::leanh::lean_dec(v___x_1910_);
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
                v___x_1926_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__13),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__13_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__13,
                );
                v___x_1927_ = lean_int_emod(v___y_1923_, v___x_1926_);
                v___x_1928_ = lean_int_ediv(v___y_1923_, v___x_1926_);
                v___x_1929_ = lean_int_emod(v___x_1928_, v___x_1926_);
                crate::leanh::lean_dec(v___x_1928_);
                v___x_1930_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__14),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__14_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__14,
                );
                v___x_1931_ = lean_int_ediv(v___y_1923_, v___x_1930_);
                crate::leanh::lean_dec(v___y_1923_);
                v___x_1932_ = lean_int_emod(v___x_1919_, v___x_1917_);
                crate::leanh::lean_dec(v___x_1919_);
                v___x_1933_ = l_Fin_succ___redArg(v___y_1921_);
                crate::leanh::lean_dec(v___y_1921_);
                v___x_1934_ = lean_nat_dec_le(v___x_1914_, v___x_1933_);
                if v___x_1934_ == 0 {
                    crate::leanh::lean_dec(v___x_1933_);
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
                crate::leanh::lean_dec(v___x_1943_);
                crate::leanh::lean_dec(v___y_1940_);
                v___x_1945_ = crate::leanh::lean_unsigned_to_nat(31);
                v_months_1946_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__28),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__28_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__28,
                );
                v___x_1947_ = crate::leanh::lean_unsigned_to_nat(0);
                v_mon_1948_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__29),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__29_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__29,
                );
                if v_isShared_1881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1880_, 1, v_mon_1948_);
                    crate::leanh::lean_ctor_set(v___x_1880_, 0, v_remDays_1944_);
                    v___x_1950_ = v___x_1880_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1972_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_remDays_1944_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_mon_1948_);
                    v___x_1950_ = v_reuseFailAlloc_1972_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1951_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(v_months_1946_, v___x_1950_);
                v_fst_1952_ = crate::leanh::lean_ctor_get(v___x_1951_, 0);
                crate::leanh::lean_inc(v_fst_1952_);
                v_snd_1953_ = crate::leanh::lean_ctor_get(v___x_1951_, 1);
                crate::leanh::lean_inc(v_snd_1953_);
                crate::leanh::lean_dec_ref(v___x_1951_);
                v___x_1954_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__30),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__30_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__30,
                );
                v___x_1955_ = lean_int_add(v___x_1954_, v_remYears_1942_);
                crate::leanh::lean_dec(v_remYears_1942_);
                v___x_1956_ = lean_int_mul(v___x_1899_, v___y_1938_);
                crate::leanh::lean_dec(v___y_1938_);
                v___x_1957_ = lean_int_add(v___x_1955_, v___x_1956_);
                crate::leanh::lean_dec(v___x_1956_);
                crate::leanh::lean_dec(v___x_1955_);
                v___x_1958_ = lean_int_mul(v___x_1897_, v___y_1937_);
                crate::leanh::lean_dec(v___y_1937_);
                v___x_1959_ = lean_int_add(v___x_1957_, v___x_1958_);
                crate::leanh::lean_dec(v___x_1958_);
                crate::leanh::lean_dec(v___x_1957_);
                v___x_1960_ = lean_int_mul(v___x_1884_, v___y_1939_);
                crate::leanh::lean_dec(v___y_1939_);
                v_year_1961_ = lean_int_add(v___x_1959_, v___x_1960_);
                crate::leanh::lean_dec(v___x_1960_);
                crate::leanh::lean_dec(v___x_1959_);
                v___x_1962_ = l_Int_toNat(v_fst_1952_);
                crate::leanh::lean_dec(v_fst_1952_);
                v___x_1963_ = lean_nat_mod(v___x_1962_, v___x_1945_);
                crate::leanh::lean_dec(v___x_1962_);
                v___x_1964_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1965_ = lean_nat_dec_lt(v___x_1964_, v_snd_1953_);
                if v___x_1965_ == 0 {
                    v___x_1966_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1967_ = lean_nat_add(v_snd_1953_, v___x_1966_);
                    crate::leanh::lean_dec(v_snd_1953_);
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
                    crate::leanh::lean_dec(v_year_1961_);
                    v___x_1970_ = lean_nat_sub(v_snd_1953_, v___x_1964_);
                    crate::leanh::lean_dec(v_snd_1953_);
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
                crate::leanh::lean_dec(v___x_1979_);
                crate::leanh::lean_dec(v___y_1975_);
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
                    crate::leanh::lean_dec(v_remYears_1981_);
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
                crate::leanh::lean_dec(v___x_1989_);
                crate::leanh::lean_dec(v___y_1986_);
                v_quadrennialCycles_1991_ = lean_int_ediv(v_remDays_1990_, v_daysPer4Y_1916_);
                v___x_1992_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v_quadrennialCycles_1991_);
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
                    crate::leanh::lean_dec(v_centenialCycles_1999_);
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
                crate::leanh::lean_dec(v_snd_2004_);
                v___x_2007_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v_remDays_2006_);
                    v_quadracentennialCycles_2010_ =
                        lean_int_sub(v_quadracentennialCycles_2005_, v___x_1915_);
                    crate::leanh::lean_dec(v_quadracentennialCycles_2005_);
                    v___y_1996_ = v_fst_2003_;
                    v_quadracentennialCycles_1997_ = v_quadracentennialCycles_2010_;
                    v_remDays_1998_ = v_remDays_2009_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_2013_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_toWallTime___closed__0,
                );
                v_boundedDaysSinceEpoch_2014_ = lean_int_div(v_snd_2012_, v___x_2013_);
                v_rawDays_2015_ = lean_int_sub(v_boundedDaysSinceEpoch_2014_, v___x_1882_);
                crate::leanh::lean_dec(v_boundedDaysSinceEpoch_2014_);
                v_h_2016_ = lean_int_mod(v_snd_2012_, v___x_2013_);
                crate::leanh::lean_dec(v_snd_2012_);
                v___x_2017_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v_h_2016_);
                    v_rawDays_2020_ = lean_int_sub(v_rawDays_2015_, v___x_1915_);
                    crate::leanh::lean_dec(v_rawDays_2015_);
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
    mut v_as_2027_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2028_: *mut crate::leanh::LeanObject,
    mut v_b_2029_: *mut crate::leanh::LeanObject,
    mut v_a_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___redArg(
        v_as_x27_2028_,
        v_b_2029_,
    );
    return v___x_2031_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0___boxed(
    mut v_as_2032_: *mut crate::leanh::LeanObject,
    mut v_as_x27_2033_: *mut crate::leanh::LeanObject,
    mut v_b_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2036_ = l_List_forIn_x27_loop___at___00Std_Time_PlainDateTime_ofWallTime_spec__0(
        v_as_2032_,
        v_as_x27_2033_,
        v_b_2034_,
        v_a_2035_,
    );
    crate::leanh::lean_dec(v_as_x27_2033_);
    crate::leanh::lean_dec(v_as_2032_);
    return v_res_2036_;
}
pub unsafe fn l_Std_Time_PlainDateTime_toEpochDay(
    mut v_pdt_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2038_ = crate::leanh::lean_ctor_get(v_pdt_2037_, 0);
    crate::leanh::lean_inc_ref(v_date_2038_);
    crate::leanh::lean_dec_ref(v_pdt_2037_);
    v___x_2039_ = l_Std_Time_PlainDate_toEpochDay(v_date_2038_);
    return v___x_2039_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofEpochDay(
    mut v_days_2040_: *mut crate::leanh::LeanObject,
    mut v_time_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2042_ = l_Std_Time_PlainDate_ofEpochDay(v_days_2040_);
    v___x_2043_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2043_, 0, v___x_2042_);
    crate::leanh::lean_ctor_set(v___x_2043_, 1, v_time_2041_);
    return v___x_2043_;
}
pub unsafe fn l_Std_Time_PlainDateTime_ofEpochDay___boxed(
    mut v_days_2044_: *mut crate::leanh::LeanObject,
    mut v_time_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2046_ = l_Std_Time_PlainDateTime_ofEpochDay(v_days_2044_, v_time_2045_);
    crate::leanh::lean_dec(v_days_2044_);
    return v_res_2046_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withWeekday(
    mut v_dt_2047_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_2048_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2049_ = crate::leanh::lean_ctor_get(v_dt_2047_, 0);
                v_time_2050_ = crate::leanh::lean_ctor_get(v_dt_2047_, 1);
                v_isSharedCheck_2058_ = (!crate::leanh::lean_is_exclusive(v_dt_2047_)) as u8;
                if v_isSharedCheck_2058_ == 0 {
                    v___x_2052_ = v_dt_2047_;
                    v_isShared_2053_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2050_);
                    crate::leanh::lean_inc(v_date_2049_);
                    crate::leanh::lean_dec(v_dt_2047_);
                    v___x_2052_ = crate::leanh::lean_box(0);
                    v_isShared_2053_ = v_isSharedCheck_2058_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2054_ =
                    l_Std_Time_PlainDate_withWeekday(v_date_2049_, v_desiredWeekday_2048_);
                if v_isShared_2053_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2054_);
                    v___x_2056_ = v___x_2052_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_time_2050_);
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
    mut v_dt_2059_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_desiredWeekday_boxed_2061_: u8 = 0;
    let mut v_res_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_2061_ = (crate::leanh::lean_unbox(v_desiredWeekday_2060_) as u8);
    v_res_2062_ = l_Std_Time_PlainDateTime_withWeekday(v_dt_2059_, v_desiredWeekday_boxed_2061_);
    return v_res_2062_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withDaysClip(
    mut v_dt_2063_: *mut crate::leanh::LeanObject,
    mut v_days_2064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v_year_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2074_: u8 = 0;
    let mut v___y_2076_: u8 = 0;
    let mut v_max_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_unused_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2104_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2065_ = crate::leanh::lean_ctor_get(v_dt_2063_, 0);
                v_time_2066_ = crate::leanh::lean_ctor_get(v_dt_2063_, 1);
                v_isSharedCheck_2104_ = (!crate::leanh::lean_is_exclusive(v_dt_2063_)) as u8;
                if v_isSharedCheck_2104_ == 0 {
                    v___x_2068_ = v_dt_2063_;
                    v_isShared_2069_ = v_isSharedCheck_2104_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2066_);
                    crate::leanh::lean_inc(v_date_2065_);
                    crate::leanh::lean_dec(v_dt_2063_);
                    v___x_2068_ = crate::leanh::lean_box(0);
                    v_isShared_2069_ = v_isSharedCheck_2104_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2070_ = crate::leanh::lean_ctor_get(v_date_2065_, 0);
                v_month_2071_ = crate::leanh::lean_ctor_get(v_date_2065_, 1);
                v_isSharedCheck_2102_ = (!crate::leanh::lean_is_exclusive(v_date_2065_)) as u8;
                if v_isSharedCheck_2102_ == 0 {
                    v_unused_2103_ = crate::leanh::lean_ctor_get(v_date_2065_, 2);
                    crate::leanh::lean_dec(v_unused_2103_);
                    v___x_2073_ = v_date_2065_;
                    v_isShared_2074_ = v_isSharedCheck_2102_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_month_2071_);
                    crate::leanh::lean_inc(v_year_2070_);
                    crate::leanh::lean_dec(v_date_2065_);
                    v___x_2073_ = crate::leanh::lean_box(0);
                    v_isShared_2074_ = v_isSharedCheck_2102_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2091_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2092_ = lean_int_mod(v_year_2070_, v___x_2091_);
                v___x_2093_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2098_ = lean_int_dec_eq(v___x_2092_, v___x_2093_);
                crate::leanh::lean_dec(v___x_2092_);
                if v___x_2098_ == 0 {
                    v___y_2076_ = v___x_2098_;
                    state = 3;
                    continue;
                } else {
                    v___x_2099_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2100_ = lean_int_mod(v_year_2070_, v___x_2099_);
                    v___x_2101_ = lean_int_dec_eq(v___x_2100_, v___x_2093_);
                    crate::leanh::lean_dec(v___x_2100_);
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
                    crate::leanh::lean_dec(v_max_2077_);
                    if v_isShared_2074_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2073_, 2, v_days_2064_);
                        v___x_2080_ = v___x_2073_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2084_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_year_2070_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 1, v_month_2071_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_days_2064_);
                        v___x_2080_ = v_reuseFailAlloc_2084_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_days_2064_);
                    if v_isShared_2074_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2073_, 2, v_max_2077_);
                        v___x_2086_ = v___x_2073_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2090_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_year_2070_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_month_2071_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_max_2077_);
                        v___x_2086_ = v_reuseFailAlloc_2090_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2069_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2068_, 0, v___x_2080_);
                    v___x_2082_ = v___x_2068_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2083_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 0, v___x_2080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_time_2066_);
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
                    crate::leanh::lean_ctor_set(v___x_2068_, 0, v___x_2086_);
                    v___x_2088_ = v___x_2068_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_time_2066_);
                    v___x_2088_ = v_reuseFailAlloc_2089_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2088_;
            }
            8 => {
                v___x_2095_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2096_ = lean_int_mod(v_year_2070_, v___x_2095_);
                v___x_2097_ = lean_int_dec_eq(v___x_2096_, v___x_2093_);
                crate::leanh::lean_dec(v___x_2096_);
                v___y_2076_ = v___x_2097_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withDaysRollOver(
    mut v_dt_2105_: *mut crate::leanh::LeanObject,
    mut v_days_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2111_: u8 = 0;
    let mut v_year_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2107_ = crate::leanh::lean_ctor_get(v_dt_2105_, 0);
                v_time_2108_ = crate::leanh::lean_ctor_get(v_dt_2105_, 1);
                v_isSharedCheck_2118_ = (!crate::leanh::lean_is_exclusive(v_dt_2105_)) as u8;
                if v_isSharedCheck_2118_ == 0 {
                    v___x_2110_ = v_dt_2105_;
                    v_isShared_2111_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2108_);
                    crate::leanh::lean_inc(v_date_2107_);
                    crate::leanh::lean_dec(v_dt_2105_);
                    v___x_2110_ = crate::leanh::lean_box(0);
                    v_isShared_2111_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2112_ = crate::leanh::lean_ctor_get(v_date_2107_, 0);
                crate::leanh::lean_inc(v_year_2112_);
                v_month_2113_ = crate::leanh::lean_ctor_get(v_date_2107_, 1);
                crate::leanh::lean_inc(v_month_2113_);
                crate::leanh::lean_dec_ref(v_date_2107_);
                v___x_2114_ =
                    l_Std_Time_PlainDate_rollOver(v_year_2112_, v_month_2113_, v_days_2106_);
                if v_isShared_2111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2110_, 0, v___x_2114_);
                    v___x_2116_ = v___x_2110_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_time_2108_);
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
    mut v_dt_2119_: *mut crate::leanh::LeanObject,
    mut v_days_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2121_ = l_Std_Time_PlainDateTime_withDaysRollOver(v_dt_2119_, v_days_2120_);
    crate::leanh::lean_dec(v_days_2120_);
    return v_res_2121_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withMonthClip(
    mut v_dt_2122_: *mut crate::leanh::LeanObject,
    mut v_month_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2128_: u8 = 0;
    let mut v_year_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2133_: u8 = 0;
    let mut v___y_2135_: u8 = 0;
    let mut v_max_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: u8 = 0;
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: u8 = 0;
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_unused_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2124_ = crate::leanh::lean_ctor_get(v_dt_2122_, 0);
                v_time_2125_ = crate::leanh::lean_ctor_get(v_dt_2122_, 1);
                v_isSharedCheck_2163_ = (!crate::leanh::lean_is_exclusive(v_dt_2122_)) as u8;
                if v_isSharedCheck_2163_ == 0 {
                    v___x_2127_ = v_dt_2122_;
                    v_isShared_2128_ = v_isSharedCheck_2163_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2125_);
                    crate::leanh::lean_inc(v_date_2124_);
                    crate::leanh::lean_dec(v_dt_2122_);
                    v___x_2127_ = crate::leanh::lean_box(0);
                    v_isShared_2128_ = v_isSharedCheck_2163_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2129_ = crate::leanh::lean_ctor_get(v_date_2124_, 0);
                v_day_2130_ = crate::leanh::lean_ctor_get(v_date_2124_, 2);
                v_isSharedCheck_2161_ = (!crate::leanh::lean_is_exclusive(v_date_2124_)) as u8;
                if v_isSharedCheck_2161_ == 0 {
                    v_unused_2162_ = crate::leanh::lean_ctor_get(v_date_2124_, 1);
                    crate::leanh::lean_dec(v_unused_2162_);
                    v___x_2132_ = v_date_2124_;
                    v_isShared_2133_ = v_isSharedCheck_2161_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_2130_);
                    crate::leanh::lean_inc(v_year_2129_);
                    crate::leanh::lean_dec(v_date_2124_);
                    v___x_2132_ = crate::leanh::lean_box(0);
                    v_isShared_2133_ = v_isSharedCheck_2161_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2150_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2151_ = lean_int_mod(v_year_2129_, v___x_2150_);
                v___x_2152_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2157_ = lean_int_dec_eq(v___x_2151_, v___x_2152_);
                crate::leanh::lean_dec(v___x_2151_);
                if v___x_2157_ == 0 {
                    v___y_2135_ = v___x_2157_;
                    state = 3;
                    continue;
                } else {
                    v___x_2158_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2159_ = lean_int_mod(v_year_2129_, v___x_2158_);
                    v___x_2160_ = lean_int_dec_eq(v___x_2159_, v___x_2152_);
                    crate::leanh::lean_dec(v___x_2159_);
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
                    crate::leanh::lean_dec(v_max_2136_);
                    if v_isShared_2133_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2132_, 1, v_month_2123_);
                        v___x_2139_ = v___x_2132_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2143_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_year_2129_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 1, v_month_2123_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2143_, 2, v_day_2130_);
                        v___x_2139_ = v_reuseFailAlloc_2143_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_2130_);
                    if v_isShared_2133_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2132_, 2, v_max_2136_);
                        crate::leanh::lean_ctor_set(v___x_2132_, 1, v_month_2123_);
                        v___x_2145_ = v___x_2132_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_year_2129_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_month_2123_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 2, v_max_2136_);
                        v___x_2145_ = v_reuseFailAlloc_2149_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2127_, 0, v___x_2139_);
                    v___x_2141_ = v___x_2127_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_time_2125_);
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
                    crate::leanh::lean_ctor_set(v___x_2127_, 0, v___x_2145_);
                    v___x_2147_ = v___x_2127_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2148_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_time_2125_);
                    v___x_2147_ = v_reuseFailAlloc_2148_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2147_;
            }
            8 => {
                v___x_2154_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2155_ = lean_int_mod(v_year_2129_, v___x_2154_);
                v___x_2156_ = lean_int_dec_eq(v___x_2155_, v___x_2152_);
                crate::leanh::lean_dec(v___x_2155_);
                v___y_2135_ = v___x_2156_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withMonthRollOver(
    mut v_dt_2164_: *mut crate::leanh::LeanObject,
    mut v_month_2165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2170_: u8 = 0;
    let mut v_year_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2166_ = crate::leanh::lean_ctor_get(v_dt_2164_, 0);
                v_time_2167_ = crate::leanh::lean_ctor_get(v_dt_2164_, 1);
                v_isSharedCheck_2177_ = (!crate::leanh::lean_is_exclusive(v_dt_2164_)) as u8;
                if v_isSharedCheck_2177_ == 0 {
                    v___x_2169_ = v_dt_2164_;
                    v_isShared_2170_ = v_isSharedCheck_2177_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2167_);
                    crate::leanh::lean_inc(v_date_2166_);
                    crate::leanh::lean_dec(v_dt_2164_);
                    v___x_2169_ = crate::leanh::lean_box(0);
                    v_isShared_2170_ = v_isSharedCheck_2177_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2171_ = crate::leanh::lean_ctor_get(v_date_2166_, 0);
                crate::leanh::lean_inc(v_year_2171_);
                v_day_2172_ = crate::leanh::lean_ctor_get(v_date_2166_, 2);
                crate::leanh::lean_inc(v_day_2172_);
                crate::leanh::lean_dec_ref(v_date_2166_);
                v___x_2173_ =
                    l_Std_Time_PlainDate_rollOver(v_year_2171_, v_month_2165_, v_day_2172_);
                crate::leanh::lean_dec(v_day_2172_);
                if v_isShared_2170_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2173_);
                    v___x_2175_ = v___x_2169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2176_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 1, v_time_2167_);
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
    mut v_dt_2178_: *mut crate::leanh::LeanObject,
    mut v_year_2179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v_month_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2189_: u8 = 0;
    let mut v___y_2191_: u8 = 0;
    let mut v_max_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: u8 = 0;
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: u8 = 0;
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_unused_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2180_ = crate::leanh::lean_ctor_get(v_dt_2178_, 0);
                v_time_2181_ = crate::leanh::lean_ctor_get(v_dt_2178_, 1);
                v_isSharedCheck_2219_ = (!crate::leanh::lean_is_exclusive(v_dt_2178_)) as u8;
                if v_isSharedCheck_2219_ == 0 {
                    v___x_2183_ = v_dt_2178_;
                    v_isShared_2184_ = v_isSharedCheck_2219_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2181_);
                    crate::leanh::lean_inc(v_date_2180_);
                    crate::leanh::lean_dec(v_dt_2178_);
                    v___x_2183_ = crate::leanh::lean_box(0);
                    v_isShared_2184_ = v_isSharedCheck_2219_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_month_2185_ = crate::leanh::lean_ctor_get(v_date_2180_, 1);
                v_day_2186_ = crate::leanh::lean_ctor_get(v_date_2180_, 2);
                v_isSharedCheck_2217_ = (!crate::leanh::lean_is_exclusive(v_date_2180_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v_unused_2218_ = crate::leanh::lean_ctor_get(v_date_2180_, 0);
                    crate::leanh::lean_dec(v_unused_2218_);
                    v___x_2188_ = v_date_2180_;
                    v_isShared_2189_ = v_isSharedCheck_2217_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_2186_);
                    crate::leanh::lean_inc(v_month_2185_);
                    crate::leanh::lean_dec(v_date_2180_);
                    v___x_2188_ = crate::leanh::lean_box(0);
                    v_isShared_2189_ = v_isSharedCheck_2217_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2206_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2207_ = lean_int_mod(v_year_2179_, v___x_2206_);
                v___x_2208_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2213_ = lean_int_dec_eq(v___x_2207_, v___x_2208_);
                crate::leanh::lean_dec(v___x_2207_);
                if v___x_2213_ == 0 {
                    v___y_2191_ = v___x_2213_;
                    state = 3;
                    continue;
                } else {
                    v___x_2214_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2215_ = lean_int_mod(v_year_2179_, v___x_2214_);
                    v___x_2216_ = lean_int_dec_eq(v___x_2215_, v___x_2208_);
                    crate::leanh::lean_dec(v___x_2215_);
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
                    crate::leanh::lean_dec(v_max_2192_);
                    if v_isShared_2189_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2188_, 0, v_year_2179_);
                        v___x_2195_ = v___x_2188_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2199_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_year_2179_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_month_2185_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_day_2186_);
                        v___x_2195_ = v_reuseFailAlloc_2199_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_2186_);
                    if v_isShared_2189_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2188_, 2, v_max_2192_);
                        crate::leanh::lean_ctor_set(v___x_2188_, 0, v_year_2179_);
                        v___x_2201_ = v___x_2188_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2205_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 0, v_year_2179_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 1, v_month_2185_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2205_, 2, v_max_2192_);
                        v___x_2201_ = v_reuseFailAlloc_2205_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2195_);
                    v___x_2197_ = v___x_2183_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2198_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_time_2181_);
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
                    crate::leanh::lean_ctor_set(v___x_2183_, 0, v___x_2201_);
                    v___x_2203_ = v___x_2183_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_time_2181_);
                    v___x_2203_ = v_reuseFailAlloc_2204_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2203_;
            }
            8 => {
                v___x_2210_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2211_ = lean_int_mod(v_year_2179_, v___x_2210_);
                v___x_2212_ = lean_int_dec_eq(v___x_2211_, v___x_2208_);
                crate::leanh::lean_dec(v___x_2211_);
                v___y_2191_ = v___x_2212_;
                state = 3;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_withYearRollOver(
    mut v_dt_2220_: *mut crate::leanh::LeanObject,
    mut v_year_2221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v_month_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2222_ = crate::leanh::lean_ctor_get(v_dt_2220_, 0);
                v_time_2223_ = crate::leanh::lean_ctor_get(v_dt_2220_, 1);
                v_isSharedCheck_2233_ = (!crate::leanh::lean_is_exclusive(v_dt_2220_)) as u8;
                if v_isSharedCheck_2233_ == 0 {
                    v___x_2225_ = v_dt_2220_;
                    v_isShared_2226_ = v_isSharedCheck_2233_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2223_);
                    crate::leanh::lean_inc(v_date_2222_);
                    crate::leanh::lean_dec(v_dt_2220_);
                    v___x_2225_ = crate::leanh::lean_box(0);
                    v_isShared_2226_ = v_isSharedCheck_2233_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_month_2227_ = crate::leanh::lean_ctor_get(v_date_2222_, 1);
                crate::leanh::lean_inc(v_month_2227_);
                v_day_2228_ = crate::leanh::lean_ctor_get(v_date_2222_, 2);
                crate::leanh::lean_inc(v_day_2228_);
                crate::leanh::lean_dec_ref(v_date_2222_);
                v___x_2229_ =
                    l_Std_Time_PlainDate_rollOver(v_year_2221_, v_month_2227_, v_day_2228_);
                crate::leanh::lean_dec(v_day_2228_);
                if v_isShared_2226_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2225_, 0, v___x_2229_);
                    v___x_2231_ = v___x_2225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v___x_2229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 1, v_time_2223_);
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
    mut v_dt_2234_: *mut crate::leanh::LeanObject,
    mut v_hour_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2240_: u8 = 0;
    let mut v_minute_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2253_: u8 = 0;
    let mut v_unused_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2236_ = crate::leanh::lean_ctor_get(v_dt_2234_, 1);
                v_date_2237_ = crate::leanh::lean_ctor_get(v_dt_2234_, 0);
                v_isSharedCheck_2255_ = (!crate::leanh::lean_is_exclusive(v_dt_2234_)) as u8;
                if v_isSharedCheck_2255_ == 0 {
                    v___x_2239_ = v_dt_2234_;
                    v_isShared_2240_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2236_);
                    crate::leanh::lean_inc(v_date_2237_);
                    crate::leanh::lean_dec(v_dt_2234_);
                    v___x_2239_ = crate::leanh::lean_box(0);
                    v_isShared_2240_ = v_isSharedCheck_2255_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_minute_2241_ = crate::leanh::lean_ctor_get(v_time_2236_, 1);
                v_second_2242_ = crate::leanh::lean_ctor_get(v_time_2236_, 2);
                v_nanosecond_2243_ = crate::leanh::lean_ctor_get(v_time_2236_, 3);
                v_isSharedCheck_2253_ = (!crate::leanh::lean_is_exclusive(v_time_2236_)) as u8;
                if v_isSharedCheck_2253_ == 0 {
                    v_unused_2254_ = crate::leanh::lean_ctor_get(v_time_2236_, 0);
                    crate::leanh::lean_dec(v_unused_2254_);
                    v___x_2245_ = v_time_2236_;
                    v_isShared_2246_ = v_isSharedCheck_2253_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_2243_);
                    crate::leanh::lean_inc(v_second_2242_);
                    crate::leanh::lean_inc(v_minute_2241_);
                    crate::leanh::lean_dec(v_time_2236_);
                    v___x_2245_ = crate::leanh::lean_box(0);
                    v_isShared_2246_ = v_isSharedCheck_2253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2245_, 0, v_hour_2235_);
                    v___x_2248_ = v___x_2245_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2252_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_hour_2235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_minute_2241_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 2, v_second_2242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2252_, 3, v_nanosecond_2243_);
                    v___x_2248_ = v_reuseFailAlloc_2252_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2239_, 1, v___x_2248_);
                    v___x_2250_ = v___x_2239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_date_2237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2248_);
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
    mut v_dt_2256_: *mut crate::leanh::LeanObject,
    mut v_minute_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v_hour_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2268_: u8 = 0;
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v_unused_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2258_ = crate::leanh::lean_ctor_get(v_dt_2256_, 1);
                v_date_2259_ = crate::leanh::lean_ctor_get(v_dt_2256_, 0);
                v_isSharedCheck_2277_ = (!crate::leanh::lean_is_exclusive(v_dt_2256_)) as u8;
                if v_isSharedCheck_2277_ == 0 {
                    v___x_2261_ = v_dt_2256_;
                    v_isShared_2262_ = v_isSharedCheck_2277_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2258_);
                    crate::leanh::lean_inc(v_date_2259_);
                    crate::leanh::lean_dec(v_dt_2256_);
                    v___x_2261_ = crate::leanh::lean_box(0);
                    v_isShared_2262_ = v_isSharedCheck_2277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2263_ = crate::leanh::lean_ctor_get(v_time_2258_, 0);
                v_second_2264_ = crate::leanh::lean_ctor_get(v_time_2258_, 2);
                v_nanosecond_2265_ = crate::leanh::lean_ctor_get(v_time_2258_, 3);
                v_isSharedCheck_2275_ = (!crate::leanh::lean_is_exclusive(v_time_2258_)) as u8;
                if v_isSharedCheck_2275_ == 0 {
                    v_unused_2276_ = crate::leanh::lean_ctor_get(v_time_2258_, 1);
                    crate::leanh::lean_dec(v_unused_2276_);
                    v___x_2267_ = v_time_2258_;
                    v_isShared_2268_ = v_isSharedCheck_2275_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_2265_);
                    crate::leanh::lean_inc(v_second_2264_);
                    crate::leanh::lean_inc(v_hour_2263_);
                    crate::leanh::lean_dec(v_time_2258_);
                    v___x_2267_ = crate::leanh::lean_box(0);
                    v_isShared_2268_ = v_isSharedCheck_2275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2267_, 1, v_minute_2257_);
                    v___x_2270_ = v___x_2267_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_hour_2263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_minute_2257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_second_2264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 3, v_nanosecond_2265_);
                    v___x_2270_ = v_reuseFailAlloc_2274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2262_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2261_, 1, v___x_2270_);
                    v___x_2272_ = v___x_2261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2273_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_date_2259_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2273_, 1, v___x_2270_);
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
    mut v_dt_2278_: *mut crate::leanh::LeanObject,
    mut v_second_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v_hour_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v_unused_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2280_ = crate::leanh::lean_ctor_get(v_dt_2278_, 1);
                v_date_2281_ = crate::leanh::lean_ctor_get(v_dt_2278_, 0);
                v_isSharedCheck_2299_ = (!crate::leanh::lean_is_exclusive(v_dt_2278_)) as u8;
                if v_isSharedCheck_2299_ == 0 {
                    v___x_2283_ = v_dt_2278_;
                    v_isShared_2284_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2280_);
                    crate::leanh::lean_inc(v_date_2281_);
                    crate::leanh::lean_dec(v_dt_2278_);
                    v___x_2283_ = crate::leanh::lean_box(0);
                    v_isShared_2284_ = v_isSharedCheck_2299_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2285_ = crate::leanh::lean_ctor_get(v_time_2280_, 0);
                v_minute_2286_ = crate::leanh::lean_ctor_get(v_time_2280_, 1);
                v_nanosecond_2287_ = crate::leanh::lean_ctor_get(v_time_2280_, 3);
                v_isSharedCheck_2297_ = (!crate::leanh::lean_is_exclusive(v_time_2280_)) as u8;
                if v_isSharedCheck_2297_ == 0 {
                    v_unused_2298_ = crate::leanh::lean_ctor_get(v_time_2280_, 2);
                    crate::leanh::lean_dec(v_unused_2298_);
                    v___x_2289_ = v_time_2280_;
                    v_isShared_2290_ = v_isSharedCheck_2297_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_2287_);
                    crate::leanh::lean_inc(v_minute_2286_);
                    crate::leanh::lean_inc(v_hour_2285_);
                    crate::leanh::lean_dec(v_time_2280_);
                    v___x_2289_ = crate::leanh::lean_box(0);
                    v_isShared_2290_ = v_isSharedCheck_2297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2289_, 2, v_second_2279_);
                    v___x_2292_ = v___x_2289_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_hour_2285_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 1, v_minute_2286_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 2, v_second_2279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 3, v_nanosecond_2287_);
                    v___x_2292_ = v_reuseFailAlloc_2296_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2284_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2283_, 1, v___x_2292_);
                    v___x_2294_ = v___x_2283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_date_2281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2292_);
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
pub unsafe fn _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2300_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_2301_ = lean_nat_to_int(v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_2303_ = lean_nat_to_int(v___x_2302_);
    return v___x_2303_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withMilliseconds(
    mut v_dt_2304_: *mut crate::leanh::LeanObject,
    mut v_millis_2305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2310_: u8 = 0;
    let mut v_hour_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2329_: u8 = 0;
    let mut v_isSharedCheck_2330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2306_ = crate::leanh::lean_ctor_get(v_dt_2304_, 1);
                v_date_2307_ = crate::leanh::lean_ctor_get(v_dt_2304_, 0);
                v_isSharedCheck_2330_ = (!crate::leanh::lean_is_exclusive(v_dt_2304_)) as u8;
                if v_isSharedCheck_2330_ == 0 {
                    v___x_2309_ = v_dt_2304_;
                    v_isShared_2310_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2306_);
                    crate::leanh::lean_inc(v_date_2307_);
                    crate::leanh::lean_dec(v_dt_2304_);
                    v___x_2309_ = crate::leanh::lean_box(0);
                    v_isShared_2310_ = v_isSharedCheck_2330_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2311_ = crate::leanh::lean_ctor_get(v_time_2306_, 0);
                v_minute_2312_ = crate::leanh::lean_ctor_get(v_time_2306_, 1);
                v_second_2313_ = crate::leanh::lean_ctor_get(v_time_2306_, 2);
                v_nanosecond_2314_ = crate::leanh::lean_ctor_get(v_time_2306_, 3);
                v_isSharedCheck_2329_ = (!crate::leanh::lean_is_exclusive(v_time_2306_)) as u8;
                if v_isSharedCheck_2329_ == 0 {
                    v___x_2316_ = v_time_2306_;
                    v_isShared_2317_ = v_isSharedCheck_2329_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_2314_);
                    crate::leanh::lean_inc(v_second_2313_);
                    crate::leanh::lean_inc(v_minute_2312_);
                    crate::leanh::lean_inc(v_hour_2311_);
                    crate::leanh::lean_dec(v_time_2306_);
                    v___x_2316_ = crate::leanh::lean_box(0);
                    v_isShared_2317_ = v_isSharedCheck_2329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2318_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_withMilliseconds___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__0,
                );
                v___x_2319_ = lean_int_emod(v_nanosecond_2314_, v___x_2318_);
                crate::leanh::lean_dec(v_nanosecond_2314_);
                v___x_2320_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once
                    ),
                    _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
                );
                v___x_2321_ = lean_int_mul(v_millis_2305_, v___x_2320_);
                v___x_2322_ = lean_int_add(v___x_2321_, v___x_2319_);
                crate::leanh::lean_dec(v___x_2319_);
                crate::leanh::lean_dec(v___x_2321_);
                if v_isShared_2317_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2316_, 3, v___x_2322_);
                    v___x_2324_ = v___x_2316_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2328_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_hour_2311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 1, v_minute_2312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 2, v_second_2313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2328_, 3, v___x_2322_);
                    v___x_2324_ = v_reuseFailAlloc_2328_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2310_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2309_, 1, v___x_2324_);
                    v___x_2326_ = v___x_2309_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_date_2307_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 1, v___x_2324_);
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
    mut v_dt_2331_: *mut crate::leanh::LeanObject,
    mut v_millis_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Std_Time_PlainDateTime_withMilliseconds(v_dt_2331_, v_millis_2332_);
    crate::leanh::lean_dec(v_millis_2332_);
    return v_res_2333_;
}
pub unsafe fn l_Std_Time_PlainDateTime_withNanoseconds(
    mut v_dt_2334_: *mut crate::leanh::LeanObject,
    mut v_nano_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v_hour_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2353_: u8 = 0;
    let mut v_unused_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2355_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_time_2336_ = crate::leanh::lean_ctor_get(v_dt_2334_, 1);
                v_date_2337_ = crate::leanh::lean_ctor_get(v_dt_2334_, 0);
                v_isSharedCheck_2355_ = (!crate::leanh::lean_is_exclusive(v_dt_2334_)) as u8;
                if v_isSharedCheck_2355_ == 0 {
                    v___x_2339_ = v_dt_2334_;
                    v_isShared_2340_ = v_isSharedCheck_2355_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2336_);
                    crate::leanh::lean_inc(v_date_2337_);
                    crate::leanh::lean_dec(v_dt_2334_);
                    v___x_2339_ = crate::leanh::lean_box(0);
                    v_isShared_2340_ = v_isSharedCheck_2355_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_hour_2341_ = crate::leanh::lean_ctor_get(v_time_2336_, 0);
                v_minute_2342_ = crate::leanh::lean_ctor_get(v_time_2336_, 1);
                v_second_2343_ = crate::leanh::lean_ctor_get(v_time_2336_, 2);
                v_isSharedCheck_2353_ = (!crate::leanh::lean_is_exclusive(v_time_2336_)) as u8;
                if v_isSharedCheck_2353_ == 0 {
                    v_unused_2354_ = crate::leanh::lean_ctor_get(v_time_2336_, 3);
                    crate::leanh::lean_dec(v_unused_2354_);
                    v___x_2345_ = v_time_2336_;
                    v_isShared_2346_ = v_isSharedCheck_2353_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_second_2343_);
                    crate::leanh::lean_inc(v_minute_2342_);
                    crate::leanh::lean_inc(v_hour_2341_);
                    crate::leanh::lean_dec(v_time_2336_);
                    v___x_2345_ = crate::leanh::lean_box(0);
                    v_isShared_2346_ = v_isSharedCheck_2353_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2345_, 3, v_nano_2335_);
                    v___x_2348_ = v___x_2345_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2352_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_hour_2341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 1, v_minute_2342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_second_2343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_nano_2335_);
                    v___x_2348_ = v_reuseFailAlloc_2352_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2340_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2339_, 1, v___x_2348_);
                    v___x_2350_ = v___x_2339_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_date_2337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2348_);
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
    mut v_dt_2356_: *mut crate::leanh::LeanObject,
    mut v_days_2357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v_dateDays_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2358_ = crate::leanh::lean_ctor_get(v_dt_2356_, 0);
                v_time_2359_ = crate::leanh::lean_ctor_get(v_dt_2356_, 1);
                v_isSharedCheck_2369_ = (!crate::leanh::lean_is_exclusive(v_dt_2356_)) as u8;
                if v_isSharedCheck_2369_ == 0 {
                    v___x_2361_ = v_dt_2356_;
                    v_isShared_2362_ = v_isSharedCheck_2369_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2359_);
                    crate::leanh::lean_inc(v_date_2358_);
                    crate::leanh::lean_dec(v_dt_2356_);
                    v___x_2361_ = crate::leanh::lean_box(0);
                    v_isShared_2362_ = v_isSharedCheck_2369_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dateDays_2363_ = l_Std_Time_PlainDate_toEpochDay(v_date_2358_);
                v___x_2364_ = lean_int_add(v_dateDays_2363_, v_days_2357_);
                crate::leanh::lean_dec(v_dateDays_2363_);
                v___x_2365_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2364_);
                crate::leanh::lean_dec(v___x_2364_);
                if v_isShared_2362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2361_, 0, v___x_2365_);
                    v___x_2367_ = v___x_2361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2365_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_time_2359_);
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
    mut v_dt_2370_: *mut crate::leanh::LeanObject,
    mut v_days_2371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2372_ = l_Std_Time_PlainDateTime_addDays(v_dt_2370_, v_days_2371_);
    crate::leanh::lean_dec(v_days_2371_);
    return v_res_2372_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subDays(
    mut v_dt_2373_: *mut crate::leanh::LeanObject,
    mut v_days_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2379_: u8 = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateDays_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2375_ = crate::leanh::lean_ctor_get(v_dt_2373_, 0);
                v_time_2376_ = crate::leanh::lean_ctor_get(v_dt_2373_, 1);
                v_isSharedCheck_2387_ = (!crate::leanh::lean_is_exclusive(v_dt_2373_)) as u8;
                if v_isSharedCheck_2387_ == 0 {
                    v___x_2378_ = v_dt_2373_;
                    v_isShared_2379_ = v_isSharedCheck_2387_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2376_);
                    crate::leanh::lean_inc(v_date_2375_);
                    crate::leanh::lean_dec(v_dt_2373_);
                    v___x_2378_ = crate::leanh::lean_box(0);
                    v_isShared_2379_ = v_isSharedCheck_2387_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2380_ = lean_int_neg(v_days_2374_);
                v_dateDays_2381_ = l_Std_Time_PlainDate_toEpochDay(v_date_2375_);
                v___x_2382_ = lean_int_add(v_dateDays_2381_, v___x_2380_);
                crate::leanh::lean_dec(v___x_2380_);
                crate::leanh::lean_dec(v_dateDays_2381_);
                v___x_2383_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2382_);
                crate::leanh::lean_dec(v___x_2382_);
                if v_isShared_2379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2378_, 0, v___x_2383_);
                    v___x_2385_ = v___x_2378_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_time_2376_);
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
    mut v_dt_2388_: *mut crate::leanh::LeanObject,
    mut v_days_2389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2390_ = l_Std_Time_PlainDateTime_subDays(v_dt_2388_, v_days_2389_);
    crate::leanh::lean_dec(v_days_2389_);
    return v_res_2390_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addWeeks___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_2392_ = lean_nat_to_int(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addWeeks(
    mut v_dt_2393_: *mut crate::leanh::LeanObject,
    mut v_weeks_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v_dateDays_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2408_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2395_ = crate::leanh::lean_ctor_get(v_dt_2393_, 0);
                v_time_2396_ = crate::leanh::lean_ctor_get(v_dt_2393_, 1);
                v_isSharedCheck_2408_ = (!crate::leanh::lean_is_exclusive(v_dt_2393_)) as u8;
                if v_isSharedCheck_2408_ == 0 {
                    v___x_2398_ = v_dt_2393_;
                    v_isShared_2399_ = v_isSharedCheck_2408_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2396_);
                    crate::leanh::lean_inc(v_date_2395_);
                    crate::leanh::lean_dec(v_dt_2393_);
                    v___x_2398_ = crate::leanh::lean_box(0);
                    v_isShared_2399_ = v_isSharedCheck_2408_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_dateDays_2400_ = l_Std_Time_PlainDate_toEpochDay(v_date_2395_);
                v___x_2401_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_addWeeks___closed__0,
                );
                v_daysToAdd_2402_ = lean_int_mul(v_weeks_2394_, v___x_2401_);
                v___x_2403_ = lean_int_add(v_dateDays_2400_, v_daysToAdd_2402_);
                crate::leanh::lean_dec(v_daysToAdd_2402_);
                crate::leanh::lean_dec(v_dateDays_2400_);
                v___x_2404_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2403_);
                crate::leanh::lean_dec(v___x_2403_);
                if v_isShared_2399_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2404_);
                    v___x_2406_ = v___x_2398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2407_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2407_, 1, v_time_2396_);
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
    mut v_dt_2409_: *mut crate::leanh::LeanObject,
    mut v_weeks_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Std_Time_PlainDateTime_addWeeks(v_dt_2409_, v_weeks_2410_);
    crate::leanh::lean_dec(v_weeks_2410_);
    return v_res_2411_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subWeeks(
    mut v_dt_2412_: *mut crate::leanh::LeanObject,
    mut v_weeks_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2418_: u8 = 0;
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dateDays_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_daysToAdd_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2414_ = crate::leanh::lean_ctor_get(v_dt_2412_, 0);
                v_time_2415_ = crate::leanh::lean_ctor_get(v_dt_2412_, 1);
                v_isSharedCheck_2428_ = (!crate::leanh::lean_is_exclusive(v_dt_2412_)) as u8;
                if v_isSharedCheck_2428_ == 0 {
                    v___x_2417_ = v_dt_2412_;
                    v_isShared_2418_ = v_isSharedCheck_2428_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2415_);
                    crate::leanh::lean_inc(v_date_2414_);
                    crate::leanh::lean_dec(v_dt_2412_);
                    v___x_2417_ = crate::leanh::lean_box(0);
                    v_isShared_2418_ = v_isSharedCheck_2428_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2419_ = lean_int_neg(v_weeks_2413_);
                v_dateDays_2420_ = l_Std_Time_PlainDate_toEpochDay(v_date_2414_);
                v___x_2421_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_PlainDateTime_addWeeks___closed__0,
                );
                v_daysToAdd_2422_ = lean_int_mul(v___x_2419_, v___x_2421_);
                crate::leanh::lean_dec(v___x_2419_);
                v___x_2423_ = lean_int_add(v_dateDays_2420_, v_daysToAdd_2422_);
                crate::leanh::lean_dec(v_daysToAdd_2422_);
                crate::leanh::lean_dec(v_dateDays_2420_);
                v___x_2424_ = l_Std_Time_PlainDate_ofEpochDay(v___x_2423_);
                crate::leanh::lean_dec(v___x_2423_);
                if v_isShared_2418_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2417_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2417_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_time_2415_);
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
    mut v_dt_2429_: *mut crate::leanh::LeanObject,
    mut v_weeks_2430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2431_ = l_Std_Time_PlainDateTime_subWeeks(v_dt_2429_, v_weeks_2430_);
    crate::leanh::lean_dec(v_weeks_2430_);
    return v_res_2431_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMonthsClip(
    mut v_dt_2432_: *mut crate::leanh::LeanObject,
    mut v_months_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2438_: u8 = 0;
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2434_ = crate::leanh::lean_ctor_get(v_dt_2432_, 0);
                v_time_2435_ = crate::leanh::lean_ctor_get(v_dt_2432_, 1);
                v_isSharedCheck_2443_ = (!crate::leanh::lean_is_exclusive(v_dt_2432_)) as u8;
                if v_isSharedCheck_2443_ == 0 {
                    v___x_2437_ = v_dt_2432_;
                    v_isShared_2438_ = v_isSharedCheck_2443_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2435_);
                    crate::leanh::lean_inc(v_date_2434_);
                    crate::leanh::lean_dec(v_dt_2432_);
                    v___x_2437_ = crate::leanh::lean_box(0);
                    v_isShared_2438_ = v_isSharedCheck_2443_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2439_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2434_, v_months_2433_);
                if v_isShared_2438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2437_, 0, v___x_2439_);
                    v___x_2441_ = v___x_2437_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2442_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2442_, 1, v_time_2435_);
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
    mut v_dt_2444_: *mut crate::leanh::LeanObject,
    mut v_months_2445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2446_ = l_Std_Time_PlainDateTime_addMonthsClip(v_dt_2444_, v_months_2445_);
    crate::leanh::lean_dec(v_months_2445_);
    return v_res_2446_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMonthsClip(
    mut v_dt_2447_: *mut crate::leanh::LeanObject,
    mut v_months_2448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2449_ = crate::leanh::lean_ctor_get(v_dt_2447_, 0);
                v_time_2450_ = crate::leanh::lean_ctor_get(v_dt_2447_, 1);
                v_isSharedCheck_2459_ = (!crate::leanh::lean_is_exclusive(v_dt_2447_)) as u8;
                if v_isSharedCheck_2459_ == 0 {
                    v___x_2452_ = v_dt_2447_;
                    v_isShared_2453_ = v_isSharedCheck_2459_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2450_);
                    crate::leanh::lean_inc(v_date_2449_);
                    crate::leanh::lean_dec(v_dt_2447_);
                    v___x_2452_ = crate::leanh::lean_box(0);
                    v_isShared_2453_ = v_isSharedCheck_2459_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2454_ = lean_int_neg(v_months_2448_);
                v___x_2455_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2449_, v___x_2454_);
                crate::leanh::lean_dec(v___x_2454_);
                if v_isShared_2453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2452_, 0, v___x_2455_);
                    v___x_2457_ = v___x_2452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_time_2450_);
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
    mut v_dt_2460_: *mut crate::leanh::LeanObject,
    mut v_months_2461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_Std_Time_PlainDateTime_subMonthsClip(v_dt_2460_, v_months_2461_);
    crate::leanh::lean_dec(v_months_2461_);
    return v_res_2462_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMonthsRollOver(
    mut v_dt_2463_: *mut crate::leanh::LeanObject,
    mut v_months_2464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2465_ = crate::leanh::lean_ctor_get(v_dt_2463_, 0);
                v_time_2466_ = crate::leanh::lean_ctor_get(v_dt_2463_, 1);
                v_isSharedCheck_2474_ = (!crate::leanh::lean_is_exclusive(v_dt_2463_)) as u8;
                if v_isSharedCheck_2474_ == 0 {
                    v___x_2468_ = v_dt_2463_;
                    v_isShared_2469_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2466_);
                    crate::leanh::lean_inc(v_date_2465_);
                    crate::leanh::lean_dec(v_dt_2463_);
                    v___x_2468_ = crate::leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2470_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2465_, v_months_2464_);
                if v_isShared_2469_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2468_, 0, v___x_2470_);
                    v___x_2472_ = v___x_2468_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_time_2466_);
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
    mut v_dt_2475_: *mut crate::leanh::LeanObject,
    mut v_months_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2477_ = l_Std_Time_PlainDateTime_addMonthsRollOver(v_dt_2475_, v_months_2476_);
    crate::leanh::lean_dec(v_months_2476_);
    return v_res_2477_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMonthsRollOver(
    mut v_dt_2478_: *mut crate::leanh::LeanObject,
    mut v_months_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2484_: u8 = 0;
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2480_ = crate::leanh::lean_ctor_get(v_dt_2478_, 0);
                v_time_2481_ = crate::leanh::lean_ctor_get(v_dt_2478_, 1);
                v_isSharedCheck_2490_ = (!crate::leanh::lean_is_exclusive(v_dt_2478_)) as u8;
                if v_isSharedCheck_2490_ == 0 {
                    v___x_2483_ = v_dt_2478_;
                    v_isShared_2484_ = v_isSharedCheck_2490_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2481_);
                    crate::leanh::lean_inc(v_date_2480_);
                    crate::leanh::lean_dec(v_dt_2478_);
                    v___x_2483_ = crate::leanh::lean_box(0);
                    v_isShared_2484_ = v_isSharedCheck_2490_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2485_ = lean_int_neg(v_months_2479_);
                v___x_2486_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2480_, v___x_2485_);
                crate::leanh::lean_dec(v___x_2485_);
                if v_isShared_2484_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2483_, 0, v___x_2486_);
                    v___x_2488_ = v___x_2483_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2489_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_time_2481_);
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
    mut v_dt_2491_: *mut crate::leanh::LeanObject,
    mut v_months_2492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2493_ = l_Std_Time_PlainDateTime_subMonthsRollOver(v_dt_2491_, v_months_2492_);
    crate::leanh::lean_dec(v_months_2492_);
    return v_res_2493_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_2495_ = lean_nat_to_int(v___x_2494_);
    return v___x_2495_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addYearsRollOver(
    mut v_dt_2496_: *mut crate::leanh::LeanObject,
    mut v_years_2497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2502_: u8 = 0;
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2509_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2498_ = crate::leanh::lean_ctor_get(v_dt_2496_, 0);
                v_time_2499_ = crate::leanh::lean_ctor_get(v_dt_2496_, 1);
                v_isSharedCheck_2509_ = (!crate::leanh::lean_is_exclusive(v_dt_2496_)) as u8;
                if v_isSharedCheck_2509_ == 0 {
                    v___x_2501_ = v_dt_2496_;
                    v_isShared_2502_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2499_);
                    crate::leanh::lean_inc(v_date_2498_);
                    crate::leanh::lean_dec(v_dt_2496_);
                    v___x_2501_ = crate::leanh::lean_box(0);
                    v_isShared_2502_ = v_isSharedCheck_2509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2503_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2504_ = lean_int_mul(v_years_2497_, v___x_2503_);
                v___x_2505_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2498_, v___x_2504_);
                crate::leanh::lean_dec(v___x_2504_);
                if v_isShared_2502_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2501_, 0, v___x_2505_);
                    v___x_2507_ = v___x_2501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___x_2505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2508_, 1, v_time_2499_);
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
    mut v_dt_2510_: *mut crate::leanh::LeanObject,
    mut v_years_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Std_Time_PlainDateTime_addYearsRollOver(v_dt_2510_, v_years_2511_);
    crate::leanh::lean_dec(v_years_2511_);
    return v_res_2512_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addYearsClip(
    mut v_dt_2513_: *mut crate::leanh::LeanObject,
    mut v_years_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2519_: u8 = 0;
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2515_ = crate::leanh::lean_ctor_get(v_dt_2513_, 0);
                v_time_2516_ = crate::leanh::lean_ctor_get(v_dt_2513_, 1);
                v_isSharedCheck_2526_ = (!crate::leanh::lean_is_exclusive(v_dt_2513_)) as u8;
                if v_isSharedCheck_2526_ == 0 {
                    v___x_2518_ = v_dt_2513_;
                    v_isShared_2519_ = v_isSharedCheck_2526_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2516_);
                    crate::leanh::lean_inc(v_date_2515_);
                    crate::leanh::lean_dec(v_dt_2513_);
                    v___x_2518_ = crate::leanh::lean_box(0);
                    v_isShared_2519_ = v_isSharedCheck_2526_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2520_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2521_ = lean_int_mul(v_years_2514_, v___x_2520_);
                v___x_2522_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2515_, v___x_2521_);
                crate::leanh::lean_dec(v___x_2521_);
                if v_isShared_2519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2518_, 0, v___x_2522_);
                    v___x_2524_ = v___x_2518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v___x_2522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_time_2516_);
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
    mut v_dt_2527_: *mut crate::leanh::LeanObject,
    mut v_years_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2529_ = l_Std_Time_PlainDateTime_addYearsClip(v_dt_2527_, v_years_2528_);
    crate::leanh::lean_dec(v_years_2528_);
    return v_res_2529_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subYearsRollOver(
    mut v_dt_2530_: *mut crate::leanh::LeanObject,
    mut v_years_2531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2532_ = crate::leanh::lean_ctor_get(v_dt_2530_, 0);
                v_time_2533_ = crate::leanh::lean_ctor_get(v_dt_2530_, 1);
                v_isSharedCheck_2544_ = (!crate::leanh::lean_is_exclusive(v_dt_2530_)) as u8;
                if v_isSharedCheck_2544_ == 0 {
                    v___x_2535_ = v_dt_2530_;
                    v_isShared_2536_ = v_isSharedCheck_2544_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2533_);
                    crate::leanh::lean_inc(v_date_2532_);
                    crate::leanh::lean_dec(v_dt_2530_);
                    v___x_2535_ = crate::leanh::lean_box(0);
                    v_isShared_2536_ = v_isSharedCheck_2544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2537_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2538_ = lean_int_mul(v_years_2531_, v___x_2537_);
                v___x_2539_ = lean_int_neg(v___x_2538_);
                crate::leanh::lean_dec(v___x_2538_);
                v___x_2540_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2532_, v___x_2539_);
                crate::leanh::lean_dec(v___x_2539_);
                if v_isShared_2536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2540_);
                    v___x_2542_ = v___x_2535_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2543_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_time_2533_);
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
    mut v_dt_2545_: *mut crate::leanh::LeanObject,
    mut v_years_2546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2547_ = l_Std_Time_PlainDateTime_subYearsRollOver(v_dt_2545_, v_years_2546_);
    crate::leanh::lean_dec(v_years_2546_);
    return v_res_2547_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subYearsClip(
    mut v_dt_2548_: *mut crate::leanh::LeanObject,
    mut v_years_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2550_ = crate::leanh::lean_ctor_get(v_dt_2548_, 0);
                v_time_2551_ = crate::leanh::lean_ctor_get(v_dt_2548_, 1);
                v_isSharedCheck_2562_ = (!crate::leanh::lean_is_exclusive(v_dt_2548_)) as u8;
                if v_isSharedCheck_2562_ == 0 {
                    v___x_2553_ = v_dt_2548_;
                    v_isShared_2554_ = v_isSharedCheck_2562_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2551_);
                    crate::leanh::lean_inc(v_date_2550_);
                    crate::leanh::lean_dec(v_dt_2548_);
                    v___x_2553_ = crate::leanh::lean_box(0);
                    v_isShared_2554_ = v_isSharedCheck_2562_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2555_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_PlainDateTime_addYearsRollOver___closed__0_once
                    ),
                    _init_l_Std_Time_PlainDateTime_addYearsRollOver___closed__0,
                );
                v___x_2556_ = lean_int_mul(v_years_2549_, v___x_2555_);
                v___x_2557_ = lean_int_neg(v___x_2556_);
                crate::leanh::lean_dec(v___x_2556_);
                v___x_2558_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2550_, v___x_2557_);
                crate::leanh::lean_dec(v___x_2557_);
                if v_isShared_2554_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2553_, 0, v___x_2558_);
                    v___x_2560_ = v___x_2553_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_time_2551_);
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
    mut v_dt_2563_: *mut crate::leanh::LeanObject,
    mut v_years_2564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2565_ = l_Std_Time_PlainDateTime_subYearsClip(v_dt_2563_, v_years_2564_);
    crate::leanh::lean_dec(v_years_2564_);
    return v_res_2565_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addNanoseconds(
    mut v_dt_2566_: *mut crate::leanh::LeanObject,
    mut v_nanos_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2568_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2566_);
    v_second_2569_ = crate::leanh::lean_ctor_get(v___x_2568_, 0);
    crate::leanh::lean_inc(v_second_2569_);
    v_nano_2570_ = crate::leanh::lean_ctor_get(v___x_2568_, 1);
    crate::leanh::lean_inc(v_nano_2570_);
    crate::leanh::lean_dec_ref(v___x_2568_);
    v___x_2571_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_2567_);
    v_second_2572_ = crate::leanh::lean_ctor_get(v___x_2571_, 0);
    crate::leanh::lean_inc(v_second_2572_);
    v_nano_2573_ = crate::leanh::lean_ctor_get(v___x_2571_, 1);
    crate::leanh::lean_inc(v_nano_2573_);
    crate::leanh::lean_dec_ref(v___x_2571_);
    v___x_2574_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2575_ = lean_int_mul(v_second_2569_, v___x_2574_);
    crate::leanh::lean_dec(v_second_2569_);
    v___x_2576_ = lean_int_add(v___x_2575_, v_nano_2570_);
    crate::leanh::lean_dec(v_nano_2570_);
    crate::leanh::lean_dec(v___x_2575_);
    v___x_2577_ = lean_int_mul(v_second_2572_, v___x_2574_);
    crate::leanh::lean_dec(v_second_2572_);
    v___x_2578_ = lean_int_add(v___x_2577_, v_nano_2573_);
    crate::leanh::lean_dec(v_nano_2573_);
    crate::leanh::lean_dec(v___x_2577_);
    v___x_2579_ = lean_int_add(v___x_2576_, v___x_2578_);
    crate::leanh::lean_dec(v___x_2578_);
    crate::leanh::lean_dec(v___x_2576_);
    v___x_2580_ = l_Std_Time_Duration_ofNanoseconds(v___x_2579_);
    crate::leanh::lean_dec(v___x_2579_);
    v___x_2581_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2580_);
    return v___x_2581_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addNanoseconds___boxed(
    mut v_dt_2582_: *mut crate::leanh::LeanObject,
    mut v_nanos_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2584_ = l_Std_Time_PlainDateTime_addNanoseconds(v_dt_2582_, v_nanos_2583_);
    crate::leanh::lean_dec(v_nanos_2583_);
    return v_res_2584_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subNanoseconds(
    mut v_dt_2585_: *mut crate::leanh::LeanObject,
    mut v_nanos_2586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2587_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2585_);
    v_second_2588_ = crate::leanh::lean_ctor_get(v___x_2587_, 0);
    crate::leanh::lean_inc(v_second_2588_);
    v_nano_2589_ = crate::leanh::lean_ctor_get(v___x_2587_, 1);
    crate::leanh::lean_inc(v_nano_2589_);
    crate::leanh::lean_dec_ref(v___x_2587_);
    v___x_2590_ = lean_int_neg(v_nanos_2586_);
    v___x_2591_ = l_Std_Time_Duration_ofNanoseconds(v___x_2590_);
    crate::leanh::lean_dec(v___x_2590_);
    v_second_2592_ = crate::leanh::lean_ctor_get(v___x_2591_, 0);
    crate::leanh::lean_inc(v_second_2592_);
    v_nano_2593_ = crate::leanh::lean_ctor_get(v___x_2591_, 1);
    crate::leanh::lean_inc(v_nano_2593_);
    crate::leanh::lean_dec_ref(v___x_2591_);
    v___x_2594_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2595_ = lean_int_mul(v_second_2588_, v___x_2594_);
    crate::leanh::lean_dec(v_second_2588_);
    v___x_2596_ = lean_int_add(v___x_2595_, v_nano_2589_);
    crate::leanh::lean_dec(v_nano_2589_);
    crate::leanh::lean_dec(v___x_2595_);
    v___x_2597_ = lean_int_mul(v_second_2592_, v___x_2594_);
    crate::leanh::lean_dec(v_second_2592_);
    v___x_2598_ = lean_int_add(v___x_2597_, v_nano_2593_);
    crate::leanh::lean_dec(v_nano_2593_);
    crate::leanh::lean_dec(v___x_2597_);
    v___x_2599_ = lean_int_add(v___x_2596_, v___x_2598_);
    crate::leanh::lean_dec(v___x_2598_);
    crate::leanh::lean_dec(v___x_2596_);
    v___x_2600_ = l_Std_Time_Duration_ofNanoseconds(v___x_2599_);
    crate::leanh::lean_dec(v___x_2599_);
    v___x_2601_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2600_);
    return v___x_2601_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subNanoseconds___boxed(
    mut v_dt_2602_: *mut crate::leanh::LeanObject,
    mut v_nanos_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ = l_Std_Time_PlainDateTime_subNanoseconds(v_dt_2602_, v_nanos_2603_);
    crate::leanh::lean_dec(v_nanos_2603_);
    return v_res_2604_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addHours___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2605_ = crate::leanh::lean_cstr_to_nat(b"3600000000000\0".as_ptr().cast());
    v___x_2606_ = lean_nat_to_int(v___x_2605_);
    return v___x_2606_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addHours(
    mut v_dt_2607_: *mut crate::leanh::LeanObject,
    mut v_hours_2608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2609_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2607_);
    v_second_2610_ = crate::leanh::lean_ctor_get(v___x_2609_, 0);
    crate::leanh::lean_inc(v_second_2610_);
    v_nano_2611_ = crate::leanh::lean_ctor_get(v___x_2609_, 1);
    crate::leanh::lean_inc(v_nano_2611_);
    crate::leanh::lean_dec_ref(v___x_2609_);
    v___x_2612_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addHours___closed__0,
    );
    v___x_2613_ = lean_int_mul(v_hours_2608_, v___x_2612_);
    v___x_2614_ = l_Std_Time_Duration_ofNanoseconds(v___x_2613_);
    crate::leanh::lean_dec(v___x_2613_);
    v_second_2615_ = crate::leanh::lean_ctor_get(v___x_2614_, 0);
    crate::leanh::lean_inc(v_second_2615_);
    v_nano_2616_ = crate::leanh::lean_ctor_get(v___x_2614_, 1);
    crate::leanh::lean_inc(v_nano_2616_);
    crate::leanh::lean_dec_ref(v___x_2614_);
    v___x_2617_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2618_ = lean_int_mul(v_second_2610_, v___x_2617_);
    crate::leanh::lean_dec(v_second_2610_);
    v___x_2619_ = lean_int_add(v___x_2618_, v_nano_2611_);
    crate::leanh::lean_dec(v_nano_2611_);
    crate::leanh::lean_dec(v___x_2618_);
    v___x_2620_ = lean_int_mul(v_second_2615_, v___x_2617_);
    crate::leanh::lean_dec(v_second_2615_);
    v___x_2621_ = lean_int_add(v___x_2620_, v_nano_2616_);
    crate::leanh::lean_dec(v_nano_2616_);
    crate::leanh::lean_dec(v___x_2620_);
    v___x_2622_ = lean_int_add(v___x_2619_, v___x_2621_);
    crate::leanh::lean_dec(v___x_2621_);
    crate::leanh::lean_dec(v___x_2619_);
    v___x_2623_ = l_Std_Time_Duration_ofNanoseconds(v___x_2622_);
    crate::leanh::lean_dec(v___x_2622_);
    v___x_2624_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2623_);
    return v___x_2624_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addHours___boxed(
    mut v_dt_2625_: *mut crate::leanh::LeanObject,
    mut v_hours_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Std_Time_PlainDateTime_addHours(v_dt_2625_, v_hours_2626_);
    crate::leanh::lean_dec(v_hours_2626_);
    return v_res_2627_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subHours(
    mut v_dt_2628_: *mut crate::leanh::LeanObject,
    mut v_hours_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2630_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2628_);
    v_second_2631_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
    crate::leanh::lean_inc(v_second_2631_);
    v_nano_2632_ = crate::leanh::lean_ctor_get(v___x_2630_, 1);
    crate::leanh::lean_inc(v_nano_2632_);
    crate::leanh::lean_dec_ref(v___x_2630_);
    v___x_2633_ = lean_int_neg(v_hours_2629_);
    v___x_2634_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addHours___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addHours___closed__0,
    );
    v___x_2635_ = lean_int_mul(v___x_2633_, v___x_2634_);
    crate::leanh::lean_dec(v___x_2633_);
    v___x_2636_ = l_Std_Time_Duration_ofNanoseconds(v___x_2635_);
    crate::leanh::lean_dec(v___x_2635_);
    v_second_2637_ = crate::leanh::lean_ctor_get(v___x_2636_, 0);
    crate::leanh::lean_inc(v_second_2637_);
    v_nano_2638_ = crate::leanh::lean_ctor_get(v___x_2636_, 1);
    crate::leanh::lean_inc(v_nano_2638_);
    crate::leanh::lean_dec_ref(v___x_2636_);
    v___x_2639_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2640_ = lean_int_mul(v_second_2631_, v___x_2639_);
    crate::leanh::lean_dec(v_second_2631_);
    v___x_2641_ = lean_int_add(v___x_2640_, v_nano_2632_);
    crate::leanh::lean_dec(v_nano_2632_);
    crate::leanh::lean_dec(v___x_2640_);
    v___x_2642_ = lean_int_mul(v_second_2637_, v___x_2639_);
    crate::leanh::lean_dec(v_second_2637_);
    v___x_2643_ = lean_int_add(v___x_2642_, v_nano_2638_);
    crate::leanh::lean_dec(v_nano_2638_);
    crate::leanh::lean_dec(v___x_2642_);
    v___x_2644_ = lean_int_add(v___x_2641_, v___x_2643_);
    crate::leanh::lean_dec(v___x_2643_);
    crate::leanh::lean_dec(v___x_2641_);
    v___x_2645_ = l_Std_Time_Duration_ofNanoseconds(v___x_2644_);
    crate::leanh::lean_dec(v___x_2644_);
    v___x_2646_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2645_);
    return v___x_2646_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subHours___boxed(
    mut v_dt_2647_: *mut crate::leanh::LeanObject,
    mut v_hours_2648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2649_ = l_Std_Time_PlainDateTime_subHours(v_dt_2647_, v_hours_2648_);
    crate::leanh::lean_dec(v_hours_2648_);
    return v_res_2649_;
}
pub unsafe fn _init_l_Std_Time_PlainDateTime_addMinutes___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2650_ = crate::leanh::lean_cstr_to_nat(b"60000000000\0".as_ptr().cast());
    v___x_2651_ = lean_nat_to_int(v___x_2650_);
    return v___x_2651_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMinutes(
    mut v_dt_2652_: *mut crate::leanh::LeanObject,
    mut v_minutes_2653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2654_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2652_);
    v_second_2655_ = crate::leanh::lean_ctor_get(v___x_2654_, 0);
    crate::leanh::lean_inc(v_second_2655_);
    v_nano_2656_ = crate::leanh::lean_ctor_get(v___x_2654_, 1);
    crate::leanh::lean_inc(v_nano_2656_);
    crate::leanh::lean_dec_ref(v___x_2654_);
    v___x_2657_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addMinutes___closed__0,
    );
    v___x_2658_ = lean_int_mul(v_minutes_2653_, v___x_2657_);
    v___x_2659_ = l_Std_Time_Duration_ofNanoseconds(v___x_2658_);
    crate::leanh::lean_dec(v___x_2658_);
    v_second_2660_ = crate::leanh::lean_ctor_get(v___x_2659_, 0);
    crate::leanh::lean_inc(v_second_2660_);
    v_nano_2661_ = crate::leanh::lean_ctor_get(v___x_2659_, 1);
    crate::leanh::lean_inc(v_nano_2661_);
    crate::leanh::lean_dec_ref(v___x_2659_);
    v___x_2662_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2663_ = lean_int_mul(v_second_2655_, v___x_2662_);
    crate::leanh::lean_dec(v_second_2655_);
    v___x_2664_ = lean_int_add(v___x_2663_, v_nano_2656_);
    crate::leanh::lean_dec(v_nano_2656_);
    crate::leanh::lean_dec(v___x_2663_);
    v___x_2665_ = lean_int_mul(v_second_2660_, v___x_2662_);
    crate::leanh::lean_dec(v_second_2660_);
    v___x_2666_ = lean_int_add(v___x_2665_, v_nano_2661_);
    crate::leanh::lean_dec(v_nano_2661_);
    crate::leanh::lean_dec(v___x_2665_);
    v___x_2667_ = lean_int_add(v___x_2664_, v___x_2666_);
    crate::leanh::lean_dec(v___x_2666_);
    crate::leanh::lean_dec(v___x_2664_);
    v___x_2668_ = l_Std_Time_Duration_ofNanoseconds(v___x_2667_);
    crate::leanh::lean_dec(v___x_2667_);
    v___x_2669_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2668_);
    return v___x_2669_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMinutes___boxed(
    mut v_dt_2670_: *mut crate::leanh::LeanObject,
    mut v_minutes_2671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_Time_PlainDateTime_addMinutes(v_dt_2670_, v_minutes_2671_);
    crate::leanh::lean_dec(v_minutes_2671_);
    return v_res_2672_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMinutes(
    mut v_dt_2673_: *mut crate::leanh::LeanObject,
    mut v_minutes_2674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2675_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2673_);
    v_second_2676_ = crate::leanh::lean_ctor_get(v___x_2675_, 0);
    crate::leanh::lean_inc(v_second_2676_);
    v_nano_2677_ = crate::leanh::lean_ctor_get(v___x_2675_, 1);
    crate::leanh::lean_inc(v_nano_2677_);
    crate::leanh::lean_dec_ref(v___x_2675_);
    v___x_2678_ = lean_int_neg(v_minutes_2674_);
    v___x_2679_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_addMinutes___closed__0_once),
        _init_l_Std_Time_PlainDateTime_addMinutes___closed__0,
    );
    v___x_2680_ = lean_int_mul(v___x_2678_, v___x_2679_);
    crate::leanh::lean_dec(v___x_2678_);
    v___x_2681_ = l_Std_Time_Duration_ofNanoseconds(v___x_2680_);
    crate::leanh::lean_dec(v___x_2680_);
    v_second_2682_ = crate::leanh::lean_ctor_get(v___x_2681_, 0);
    crate::leanh::lean_inc(v_second_2682_);
    v_nano_2683_ = crate::leanh::lean_ctor_get(v___x_2681_, 1);
    crate::leanh::lean_inc(v_nano_2683_);
    crate::leanh::lean_dec_ref(v___x_2681_);
    v___x_2684_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2685_ = lean_int_mul(v_second_2676_, v___x_2684_);
    crate::leanh::lean_dec(v_second_2676_);
    v___x_2686_ = lean_int_add(v___x_2685_, v_nano_2677_);
    crate::leanh::lean_dec(v_nano_2677_);
    crate::leanh::lean_dec(v___x_2685_);
    v___x_2687_ = lean_int_mul(v_second_2682_, v___x_2684_);
    crate::leanh::lean_dec(v_second_2682_);
    v___x_2688_ = lean_int_add(v___x_2687_, v_nano_2683_);
    crate::leanh::lean_dec(v_nano_2683_);
    crate::leanh::lean_dec(v___x_2687_);
    v___x_2689_ = lean_int_add(v___x_2686_, v___x_2688_);
    crate::leanh::lean_dec(v___x_2688_);
    crate::leanh::lean_dec(v___x_2686_);
    v___x_2690_ = l_Std_Time_Duration_ofNanoseconds(v___x_2689_);
    crate::leanh::lean_dec(v___x_2689_);
    v___x_2691_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2690_);
    return v___x_2691_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMinutes___boxed(
    mut v_dt_2692_: *mut crate::leanh::LeanObject,
    mut v_minutes_2693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2694_ = l_Std_Time_PlainDateTime_subMinutes(v_dt_2692_, v_minutes_2693_);
    crate::leanh::lean_dec(v_minutes_2693_);
    return v_res_2694_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addSeconds(
    mut v_dt_2695_: *mut crate::leanh::LeanObject,
    mut v_seconds_2696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2697_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2695_);
    v_second_2698_ = crate::leanh::lean_ctor_get(v___x_2697_, 0);
    crate::leanh::lean_inc(v_second_2698_);
    v_nano_2699_ = crate::leanh::lean_ctor_get(v___x_2697_, 1);
    crate::leanh::lean_inc(v_nano_2699_);
    crate::leanh::lean_dec_ref(v___x_2697_);
    v___x_2700_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2701_ = lean_int_mul(v_seconds_2696_, v___x_2700_);
    v___x_2702_ = l_Std_Time_Duration_ofNanoseconds(v___x_2701_);
    crate::leanh::lean_dec(v___x_2701_);
    v_second_2703_ = crate::leanh::lean_ctor_get(v___x_2702_, 0);
    crate::leanh::lean_inc(v_second_2703_);
    v_nano_2704_ = crate::leanh::lean_ctor_get(v___x_2702_, 1);
    crate::leanh::lean_inc(v_nano_2704_);
    crate::leanh::lean_dec_ref(v___x_2702_);
    v___x_2705_ = lean_int_mul(v_second_2698_, v___x_2700_);
    crate::leanh::lean_dec(v_second_2698_);
    v___x_2706_ = lean_int_add(v___x_2705_, v_nano_2699_);
    crate::leanh::lean_dec(v_nano_2699_);
    crate::leanh::lean_dec(v___x_2705_);
    v___x_2707_ = lean_int_mul(v_second_2703_, v___x_2700_);
    crate::leanh::lean_dec(v_second_2703_);
    v___x_2708_ = lean_int_add(v___x_2707_, v_nano_2704_);
    crate::leanh::lean_dec(v_nano_2704_);
    crate::leanh::lean_dec(v___x_2707_);
    v___x_2709_ = lean_int_add(v___x_2706_, v___x_2708_);
    crate::leanh::lean_dec(v___x_2708_);
    crate::leanh::lean_dec(v___x_2706_);
    v___x_2710_ = l_Std_Time_Duration_ofNanoseconds(v___x_2709_);
    crate::leanh::lean_dec(v___x_2709_);
    v___x_2711_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2710_);
    return v___x_2711_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addSeconds___boxed(
    mut v_dt_2712_: *mut crate::leanh::LeanObject,
    mut v_seconds_2713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2714_ = l_Std_Time_PlainDateTime_addSeconds(v_dt_2712_, v_seconds_2713_);
    crate::leanh::lean_dec(v_seconds_2713_);
    return v_res_2714_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subSeconds(
    mut v_dt_2715_: *mut crate::leanh::LeanObject,
    mut v_seconds_2716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2717_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2715_);
    v_second_2718_ = crate::leanh::lean_ctor_get(v___x_2717_, 0);
    crate::leanh::lean_inc(v_second_2718_);
    v_nano_2719_ = crate::leanh::lean_ctor_get(v___x_2717_, 1);
    crate::leanh::lean_inc(v_nano_2719_);
    crate::leanh::lean_dec_ref(v___x_2717_);
    v___x_2720_ = lean_int_neg(v_seconds_2716_);
    v___x_2721_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2722_ = lean_int_mul(v___x_2720_, v___x_2721_);
    crate::leanh::lean_dec(v___x_2720_);
    v___x_2723_ = l_Std_Time_Duration_ofNanoseconds(v___x_2722_);
    crate::leanh::lean_dec(v___x_2722_);
    v_second_2724_ = crate::leanh::lean_ctor_get(v___x_2723_, 0);
    crate::leanh::lean_inc(v_second_2724_);
    v_nano_2725_ = crate::leanh::lean_ctor_get(v___x_2723_, 1);
    crate::leanh::lean_inc(v_nano_2725_);
    crate::leanh::lean_dec_ref(v___x_2723_);
    v___x_2726_ = lean_int_mul(v_second_2718_, v___x_2721_);
    crate::leanh::lean_dec(v_second_2718_);
    v___x_2727_ = lean_int_add(v___x_2726_, v_nano_2719_);
    crate::leanh::lean_dec(v_nano_2719_);
    crate::leanh::lean_dec(v___x_2726_);
    v___x_2728_ = lean_int_mul(v_second_2724_, v___x_2721_);
    crate::leanh::lean_dec(v_second_2724_);
    v___x_2729_ = lean_int_add(v___x_2728_, v_nano_2725_);
    crate::leanh::lean_dec(v_nano_2725_);
    crate::leanh::lean_dec(v___x_2728_);
    v___x_2730_ = lean_int_add(v___x_2727_, v___x_2729_);
    crate::leanh::lean_dec(v___x_2729_);
    crate::leanh::lean_dec(v___x_2727_);
    v___x_2731_ = l_Std_Time_Duration_ofNanoseconds(v___x_2730_);
    crate::leanh::lean_dec(v___x_2730_);
    v___x_2732_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2731_);
    return v___x_2732_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subSeconds___boxed(
    mut v_dt_2733_: *mut crate::leanh::LeanObject,
    mut v_seconds_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2735_ = l_Std_Time_PlainDateTime_subSeconds(v_dt_2733_, v_seconds_2734_);
    crate::leanh::lean_dec(v_seconds_2734_);
    return v_res_2735_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMilliseconds(
    mut v_dt_2736_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2738_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2736_);
    v_second_2739_ = crate::leanh::lean_ctor_get(v___x_2738_, 0);
    crate::leanh::lean_inc(v_second_2739_);
    v_nano_2740_ = crate::leanh::lean_ctor_get(v___x_2738_, 1);
    crate::leanh::lean_inc(v_nano_2740_);
    crate::leanh::lean_dec_ref(v___x_2738_);
    v___x_2741_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
    );
    v___x_2742_ = lean_int_mul(v_milliseconds_2737_, v___x_2741_);
    v___x_2743_ = l_Std_Time_Duration_ofNanoseconds(v___x_2742_);
    crate::leanh::lean_dec(v___x_2742_);
    v_second_2744_ = crate::leanh::lean_ctor_get(v___x_2743_, 0);
    crate::leanh::lean_inc(v_second_2744_);
    v_nano_2745_ = crate::leanh::lean_ctor_get(v___x_2743_, 1);
    crate::leanh::lean_inc(v_nano_2745_);
    crate::leanh::lean_dec_ref(v___x_2743_);
    v___x_2746_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2747_ = lean_int_mul(v_second_2739_, v___x_2746_);
    crate::leanh::lean_dec(v_second_2739_);
    v___x_2748_ = lean_int_add(v___x_2747_, v_nano_2740_);
    crate::leanh::lean_dec(v_nano_2740_);
    crate::leanh::lean_dec(v___x_2747_);
    v___x_2749_ = lean_int_mul(v_second_2744_, v___x_2746_);
    crate::leanh::lean_dec(v_second_2744_);
    v___x_2750_ = lean_int_add(v___x_2749_, v_nano_2745_);
    crate::leanh::lean_dec(v_nano_2745_);
    crate::leanh::lean_dec(v___x_2749_);
    v___x_2751_ = lean_int_add(v___x_2748_, v___x_2750_);
    crate::leanh::lean_dec(v___x_2750_);
    crate::leanh::lean_dec(v___x_2748_);
    v___x_2752_ = l_Std_Time_Duration_ofNanoseconds(v___x_2751_);
    crate::leanh::lean_dec(v___x_2751_);
    v___x_2753_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2752_);
    return v___x_2753_;
}
pub unsafe fn l_Std_Time_PlainDateTime_addMilliseconds___boxed(
    mut v_dt_2754_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2756_ = l_Std_Time_PlainDateTime_addMilliseconds(v_dt_2754_, v_milliseconds_2755_);
    crate::leanh::lean_dec(v_milliseconds_2755_);
    return v_res_2756_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMilliseconds(
    mut v_dt_2757_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Std_Time_PlainDateTime_toWallTime(v_dt_2757_);
    v_second_2760_ = crate::leanh::lean_ctor_get(v___x_2759_, 0);
    crate::leanh::lean_inc(v_second_2760_);
    v_nano_2761_ = crate::leanh::lean_ctor_get(v___x_2759_, 1);
    crate::leanh::lean_inc(v_nano_2761_);
    crate::leanh::lean_dec_ref(v___x_2759_);
    v___x_2762_ = lean_int_neg(v_milliseconds_2758_);
    v___x_2763_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
    );
    v___x_2764_ = lean_int_mul(v___x_2762_, v___x_2763_);
    crate::leanh::lean_dec(v___x_2762_);
    v___x_2765_ = l_Std_Time_Duration_ofNanoseconds(v___x_2764_);
    crate::leanh::lean_dec(v___x_2764_);
    v_second_2766_ = crate::leanh::lean_ctor_get(v___x_2765_, 0);
    crate::leanh::lean_inc(v_second_2766_);
    v_nano_2767_ = crate::leanh::lean_ctor_get(v___x_2765_, 1);
    crate::leanh::lean_inc(v_nano_2767_);
    crate::leanh::lean_dec_ref(v___x_2765_);
    v___x_2768_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2769_ = lean_int_mul(v_second_2760_, v___x_2768_);
    crate::leanh::lean_dec(v_second_2760_);
    v___x_2770_ = lean_int_add(v___x_2769_, v_nano_2761_);
    crate::leanh::lean_dec(v_nano_2761_);
    crate::leanh::lean_dec(v___x_2769_);
    v___x_2771_ = lean_int_mul(v_second_2766_, v___x_2768_);
    crate::leanh::lean_dec(v_second_2766_);
    v___x_2772_ = lean_int_add(v___x_2771_, v_nano_2767_);
    crate::leanh::lean_dec(v_nano_2767_);
    crate::leanh::lean_dec(v___x_2771_);
    v___x_2773_ = lean_int_add(v___x_2770_, v___x_2772_);
    crate::leanh::lean_dec(v___x_2772_);
    crate::leanh::lean_dec(v___x_2770_);
    v___x_2774_ = l_Std_Time_Duration_ofNanoseconds(v___x_2773_);
    crate::leanh::lean_dec(v___x_2773_);
    v___x_2775_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2774_);
    return v___x_2775_;
}
pub unsafe fn l_Std_Time_PlainDateTime_subMilliseconds___boxed(
    mut v_dt_2776_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2778_ = l_Std_Time_PlainDateTime_subMilliseconds(v_dt_2776_, v_milliseconds_2777_);
    crate::leanh::lean_dec(v_milliseconds_2777_);
    return v_res_2778_;
}
pub unsafe fn l_Std_Time_PlainDateTime_year(
    mut v_dt_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2780_ = crate::leanh::lean_ctor_get(v_dt_2779_, 0);
    v_year_2781_ = crate::leanh::lean_ctor_get(v_date_2780_, 0);
    crate::leanh::lean_inc(v_year_2781_);
    return v_year_2781_;
}
pub unsafe fn l_Std_Time_PlainDateTime_year___boxed(
    mut v_dt_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2783_ = l_Std_Time_PlainDateTime_year(v_dt_2782_);
    crate::leanh::lean_dec_ref(v_dt_2782_);
    return v_res_2783_;
}
pub unsafe fn l_Std_Time_PlainDateTime_month(
    mut v_dt_2784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2785_ = crate::leanh::lean_ctor_get(v_dt_2784_, 0);
    v_month_2786_ = crate::leanh::lean_ctor_get(v_date_2785_, 1);
    crate::leanh::lean_inc(v_month_2786_);
    return v_month_2786_;
}
pub unsafe fn l_Std_Time_PlainDateTime_month___boxed(
    mut v_dt_2787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2788_ = l_Std_Time_PlainDateTime_month(v_dt_2787_);
    crate::leanh::lean_dec_ref(v_dt_2787_);
    return v_res_2788_;
}
pub unsafe fn l_Std_Time_PlainDateTime_day(
    mut v_dt_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2790_ = crate::leanh::lean_ctor_get(v_dt_2789_, 0);
    v_day_2791_ = crate::leanh::lean_ctor_get(v_date_2790_, 2);
    crate::leanh::lean_inc(v_day_2791_);
    return v_day_2791_;
}
pub unsafe fn l_Std_Time_PlainDateTime_day___boxed(
    mut v_dt_2792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2793_ = l_Std_Time_PlainDateTime_day(v_dt_2792_);
    crate::leanh::lean_dec_ref(v_dt_2792_);
    return v_res_2793_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekday(
    mut v_dt_2794_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: u8 = 0;
    v_date_2795_ = crate::leanh::lean_ctor_get(v_dt_2794_, 0);
    crate::leanh::lean_inc_ref(v_date_2795_);
    crate::leanh::lean_dec_ref(v_dt_2794_);
    v___x_2796_ = l_Std_Time_PlainDate_weekday(v_date_2795_);
    return v___x_2796_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekday___boxed(
    mut v_dt_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2798_: u8 = 0;
    let mut v_r_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Std_Time_PlainDateTime_weekday(v_dt_2797_);
    v_r_2799_ = crate::leanh::lean_box((v_res_2798_) as usize);
    return v_r_2799_;
}
pub unsafe fn l_Std_Time_PlainDateTime_hour(
    mut v_dt_2800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_time_2801_ = crate::leanh::lean_ctor_get(v_dt_2800_, 1);
    v_hour_2802_ = crate::leanh::lean_ctor_get(v_time_2801_, 0);
    crate::leanh::lean_inc(v_hour_2802_);
    return v_hour_2802_;
}
pub unsafe fn l_Std_Time_PlainDateTime_hour___boxed(
    mut v_dt_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2804_ = l_Std_Time_PlainDateTime_hour(v_dt_2803_);
    crate::leanh::lean_dec_ref(v_dt_2803_);
    return v_res_2804_;
}
pub unsafe fn l_Std_Time_PlainDateTime_minute(
    mut v_dt_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_time_2806_ = crate::leanh::lean_ctor_get(v_dt_2805_, 1);
    v_minute_2807_ = crate::leanh::lean_ctor_get(v_time_2806_, 1);
    crate::leanh::lean_inc(v_minute_2807_);
    return v_minute_2807_;
}
pub unsafe fn l_Std_Time_PlainDateTime_minute___boxed(
    mut v_dt_2808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2809_ = l_Std_Time_PlainDateTime_minute(v_dt_2808_);
    crate::leanh::lean_dec_ref(v_dt_2808_);
    return v_res_2809_;
}
pub unsafe fn l_Std_Time_PlainDateTime_millisecond(
    mut v_dt_2810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_time_2811_ = crate::leanh::lean_ctor_get(v_dt_2810_, 1);
    v_nanosecond_2812_ = crate::leanh::lean_ctor_get(v_time_2811_, 3);
    v___x_2813_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_withMilliseconds___closed__1_once),
        _init_l_Std_Time_PlainDateTime_withMilliseconds___closed__1,
    );
    v___x_2814_ = lean_int_ediv(v_nanosecond_2812_, v___x_2813_);
    return v___x_2814_;
}
pub unsafe fn l_Std_Time_PlainDateTime_millisecond___boxed(
    mut v_dt_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2816_ = l_Std_Time_PlainDateTime_millisecond(v_dt_2815_);
    crate::leanh::lean_dec_ref(v_dt_2815_);
    return v_res_2816_;
}
pub unsafe fn l_Std_Time_PlainDateTime_second(
    mut v_dt_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_time_2818_ = crate::leanh::lean_ctor_get(v_dt_2817_, 1);
    v_second_2819_ = crate::leanh::lean_ctor_get(v_time_2818_, 2);
    crate::leanh::lean_inc(v_second_2819_);
    return v_second_2819_;
}
pub unsafe fn l_Std_Time_PlainDateTime_second___boxed(
    mut v_dt_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2821_ = l_Std_Time_PlainDateTime_second(v_dt_2820_);
    crate::leanh::lean_dec_ref(v_dt_2820_);
    return v_res_2821_;
}
pub unsafe fn l_Std_Time_PlainDateTime_nanosecond(
    mut v_dt_2822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_time_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_time_2823_ = crate::leanh::lean_ctor_get(v_dt_2822_, 1);
    v_nanosecond_2824_ = crate::leanh::lean_ctor_get(v_time_2823_, 3);
    crate::leanh::lean_inc(v_nanosecond_2824_);
    return v_nanosecond_2824_;
}
pub unsafe fn l_Std_Time_PlainDateTime_nanosecond___boxed(
    mut v_dt_2825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2826_ = l_Std_Time_PlainDateTime_nanosecond(v_dt_2825_);
    crate::leanh::lean_dec_ref(v_dt_2825_);
    return v_res_2826_;
}
pub unsafe fn l_Std_Time_PlainDateTime_era(mut v_date_2827_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_date_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: u8 = 0;
    v_date_2828_ = crate::leanh::lean_ctor_get(v_date_2827_, 0);
    v_year_2829_ = crate::leanh::lean_ctor_get(v_date_2828_, 0);
    v___x_2830_ = l_Std_Time_Year_Offset_era(v_year_2829_);
    return v___x_2830_;
}
pub unsafe fn l_Std_Time_PlainDateTime_era___boxed(
    mut v_date_2831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2832_: u8 = 0;
    let mut v_r_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l_Std_Time_PlainDateTime_era(v_date_2831_);
    crate::leanh::lean_dec_ref(v_date_2831_);
    v_r_2833_ = crate::leanh::lean_box((v_res_2832_) as usize);
    return v_r_2833_;
}
pub unsafe fn l_Std_Time_PlainDateTime_inLeapYear(
    mut v_date_2834_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: u8 = 0;
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2835_ = crate::leanh::lean_ctor_get(v_date_2834_, 0);
                v_year_2836_ = crate::leanh::lean_ctor_get(v_date_2835_, 0);
                v___x_2837_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2838_ = lean_int_mod(v_year_2836_, v___x_2837_);
                v___x_2839_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2844_ = lean_int_dec_eq(v___x_2838_, v___x_2839_);
                crate::leanh::lean_dec(v___x_2838_);
                if v___x_2844_ == 0 {
                    return v___x_2844_;
                } else {
                    v___x_2845_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2846_ = lean_int_mod(v_year_2836_, v___x_2845_);
                    v___x_2847_ = lean_int_dec_eq(v___x_2846_, v___x_2839_);
                    crate::leanh::lean_dec(v___x_2846_);
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
                v___x_2841_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2842_ = lean_int_mod(v_year_2836_, v___x_2841_);
                v___x_2843_ = lean_int_dec_eq(v___x_2842_, v___x_2839_);
                crate::leanh::lean_dec(v___x_2842_);
                return v___x_2843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_inLeapYear___boxed(
    mut v_date_2848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2849_: u8 = 0;
    let mut v_r_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2849_ = l_Std_Time_PlainDateTime_inLeapYear(v_date_2848_);
    crate::leanh::lean_dec_ref(v_date_2848_);
    v_r_2850_ = crate::leanh::lean_box((v_res_2849_) as usize);
    return v_r_2850_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfYear(
    mut v_date_2851_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2852_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2853_ = crate::leanh::lean_ctor_get(v_date_2851_, 0);
    crate::leanh::lean_inc_ref(v_date_2853_);
    crate::leanh::lean_dec_ref(v_date_2851_);
    v___x_2854_ = l_Std_Time_PlainDate_weekOfYear(v_date_2853_, v_firstDay_2852_);
    return v___x_2854_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfYear___boxed(
    mut v_date_2855_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2857_: u8 = 0;
    let mut v_res_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2857_ = (crate::leanh::lean_unbox(v_firstDay_2856_) as u8);
    v_res_2858_ = l_Std_Time_PlainDateTime_weekOfYear(v_date_2855_, v_firstDay_boxed_2857_);
    return v_res_2858_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekYear(
    mut v_date_2859_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2860_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2861_ = crate::leanh::lean_ctor_get(v_date_2859_, 0);
    crate::leanh::lean_inc_ref(v_date_2861_);
    crate::leanh::lean_dec_ref(v_date_2859_);
    v___x_2862_ = l_Std_Time_PlainDate_weekYear(v_date_2861_, v_firstDay_2860_);
    return v___x_2862_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekYear___boxed(
    mut v_date_2863_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2865_: u8 = 0;
    let mut v_res_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2865_ = (crate::leanh::lean_unbox(v_firstDay_2864_) as u8);
    v_res_2866_ = l_Std_Time_PlainDateTime_weekYear(v_date_2863_, v_firstDay_boxed_2865_);
    return v_res_2866_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfMonth(
    mut v_date_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2868_ = crate::leanh::lean_ctor_get(v_date_2867_, 0);
    v___x_2869_ = l_Std_Time_PlainDate_weekOfMonth(v_date_2868_);
    return v___x_2869_;
}
pub unsafe fn l_Std_Time_PlainDateTime_weekOfMonth___boxed(
    mut v_date_2870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2871_ = l_Std_Time_PlainDateTime_weekOfMonth(v_date_2870_);
    crate::leanh::lean_dec_ref(v_date_2870_);
    return v_res_2871_;
}
pub unsafe fn l_Std_Time_PlainDateTime_alignedWeekOfMonth(
    mut v_date_2872_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2873_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2874_ = crate::leanh::lean_ctor_get(v_date_2872_, 0);
    crate::leanh::lean_inc_ref(v_date_2874_);
    crate::leanh::lean_dec_ref(v_date_2872_);
    v___x_2875_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_2874_, v_firstDay_2873_);
    return v___x_2875_;
}
pub unsafe fn l_Std_Time_PlainDateTime_alignedWeekOfMonth___boxed(
    mut v_date_2876_: *mut crate::leanh::LeanObject,
    mut v_firstDay_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_2878_: u8 = 0;
    let mut v_res_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_2878_ = (crate::leanh::lean_unbox(v_firstDay_2877_) as u8);
    v_res_2879_ = l_Std_Time_PlainDateTime_alignedWeekOfMonth(v_date_2876_, v_firstDay_boxed_2878_);
    return v_res_2879_;
}
pub unsafe fn l_Std_Time_PlainDateTime_dayOfYear(
    mut v_date_2880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v_year_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: u8 = 0;
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: u8 = 0;
    let mut v___x_2901_: u8 = 0;
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: u8 = 0;
    let mut v_isSharedCheck_2905_: u8 = 0;
    let mut v_unused_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2881_ = crate::leanh::lean_ctor_get(v_date_2880_, 0);
                v_isSharedCheck_2905_ = (!crate::leanh::lean_is_exclusive(v_date_2880_)) as u8;
                if v_isSharedCheck_2905_ == 0 {
                    v_unused_2906_ = crate::leanh::lean_ctor_get(v_date_2880_, 1);
                    crate::leanh::lean_dec(v_unused_2906_);
                    v___x_2883_ = v_date_2880_;
                    v_isShared_2884_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_2881_);
                    crate::leanh::lean_dec(v_date_2880_);
                    v___x_2883_ = crate::leanh::lean_box(0);
                    v_isShared_2884_ = v_isSharedCheck_2905_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_year_2885_ = crate::leanh::lean_ctor_get(v_date_2881_, 0);
                crate::leanh::lean_inc(v_year_2885_);
                v_month_2886_ = crate::leanh::lean_ctor_get(v_date_2881_, 1);
                crate::leanh::lean_inc(v_month_2886_);
                v_day_2887_ = crate::leanh::lean_ctor_get(v_date_2881_, 2);
                crate::leanh::lean_inc(v_day_2887_);
                crate::leanh::lean_dec_ref(v_date_2881_);
                v___x_2894_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__10_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__10,
                );
                v___x_2895_ = lean_int_mod(v_year_2885_, v___x_2894_);
                v___x_2896_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_instInhabitedPlainDateTime_default___closed__0_once
                    ),
                    _init_l_Std_Time_instInhabitedPlainDateTime_default___closed__0,
                );
                v___x_2901_ = lean_int_dec_eq(v___x_2895_, v___x_2896_);
                crate::leanh::lean_dec(v___x_2895_);
                if v___x_2901_ == 0 {
                    crate::leanh::lean_dec(v_year_2885_);
                    v___y_2889_ = v___x_2901_;
                    state = 2;
                    continue;
                } else {
                    v___x_2902_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_PlainDateTime_ofWallTime___closed__6_once
                        ),
                        _init_l_Std_Time_PlainDateTime_ofWallTime___closed__6,
                    );
                    v___x_2903_ = lean_int_mod(v_year_2885_, v___x_2902_);
                    v___x_2904_ = lean_int_dec_eq(v___x_2903_, v___x_2896_);
                    crate::leanh::lean_dec(v___x_2903_);
                    if v___x_2904_ == 0 {
                        if v___x_2901_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_year_2885_);
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
                    crate::leanh::lean_ctor_set(v___x_2883_, 1, v_day_2887_);
                    crate::leanh::lean_ctor_set(v___x_2883_, 0, v_month_2886_);
                    v___x_2891_ = v___x_2883_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2893_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_month_2886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2893_, 1, v_day_2887_);
                    v___x_2891_ = v_reuseFailAlloc_2893_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2892_ = l_Std_Time_ValidDate_dayOfYear(v___y_2889_, v___x_2891_);
                crate::leanh::lean_dec_ref(v___x_2891_);
                return v___x_2892_;
            }
            4 => {
                v___x_2898_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_ofWallTime___closed__2_once),
                    _init_l_Std_Time_PlainDateTime_ofWallTime___closed__2,
                );
                v___x_2899_ = lean_int_mod(v_year_2885_, v___x_2898_);
                crate::leanh::lean_dec(v_year_2885_);
                v___x_2900_ = lean_int_dec_eq(v___x_2899_, v___x_2896_);
                crate::leanh::lean_dec(v___x_2899_);
                v___y_2889_ = v___x_2900_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_PlainDateTime_quarter(
    mut v_date_2907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2908_ = crate::leanh::lean_ctor_get(v_date_2907_, 0);
    v___x_2909_ = l_Std_Time_PlainDate_quarter(v_date_2908_);
    return v___x_2909_;
}
pub unsafe fn l_Std_Time_PlainDateTime_quarter___boxed(
    mut v_date_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2911_ = l_Std_Time_PlainDateTime_quarter(v_date_2910_);
    crate::leanh::lean_dec_ref(v_date_2910_);
    return v_res_2911_;
}
pub unsafe fn l_Std_Time_PlainDateTime_atTime(
    mut v_date_2912_: *mut crate::leanh::LeanObject,
    mut v_time_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2914_, 0, v_date_2912_);
    crate::leanh::lean_ctor_set(v___x_2914_, 1, v_time_2913_);
    return v___x_2914_;
}
pub unsafe fn l_Std_Time_PlainDateTime_atDate(
    mut v_time_2915_: *mut crate::leanh::LeanObject,
    mut v_date_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2917_, 0, v_date_2916_);
    crate::leanh::lean_ctor_set(v___x_2917_, 1, v_time_2915_);
    return v___x_2917_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instHAddDuration___lam__0(
    mut v_x_2946_: *mut crate::leanh::LeanObject,
    mut v_y_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_second_2948_ = crate::leanh::lean_ctor_get(v_y_2947_, 0);
    v_nano_2949_ = crate::leanh::lean_ctor_get(v_y_2947_, 1);
    v___x_2950_ = l_Std_Time_PlainDateTime_toWallTime(v_x_2946_);
    v_second_2951_ = crate::leanh::lean_ctor_get(v___x_2950_, 0);
    crate::leanh::lean_inc(v_second_2951_);
    v_nano_2952_ = crate::leanh::lean_ctor_get(v___x_2950_, 1);
    crate::leanh::lean_inc(v_nano_2952_);
    crate::leanh::lean_dec_ref(v___x_2950_);
    v___x_2953_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_PlainDateTime_toWallTime___closed__1_once),
        _init_l_Std_Time_PlainDateTime_toWallTime___closed__1,
    );
    v___x_2954_ = lean_int_mul(v_second_2948_, v___x_2953_);
    v_nanos_2955_ = lean_int_add(v___x_2954_, v_nano_2949_);
    crate::leanh::lean_dec(v___x_2954_);
    v___x_2956_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_2955_);
    crate::leanh::lean_dec(v_nanos_2955_);
    v_second_2957_ = crate::leanh::lean_ctor_get(v___x_2956_, 0);
    crate::leanh::lean_inc(v_second_2957_);
    v_nano_2958_ = crate::leanh::lean_ctor_get(v___x_2956_, 1);
    crate::leanh::lean_inc(v_nano_2958_);
    crate::leanh::lean_dec_ref(v___x_2956_);
    v___x_2959_ = lean_int_mul(v_second_2951_, v___x_2953_);
    crate::leanh::lean_dec(v_second_2951_);
    v___x_2960_ = lean_int_add(v___x_2959_, v_nano_2952_);
    crate::leanh::lean_dec(v_nano_2952_);
    crate::leanh::lean_dec(v___x_2959_);
    v___x_2961_ = lean_int_mul(v_second_2957_, v___x_2953_);
    crate::leanh::lean_dec(v_second_2957_);
    v___x_2962_ = lean_int_add(v___x_2961_, v_nano_2958_);
    crate::leanh::lean_dec(v_nano_2958_);
    crate::leanh::lean_dec(v___x_2961_);
    v___x_2963_ = lean_int_add(v___x_2960_, v___x_2962_);
    crate::leanh::lean_dec(v___x_2962_);
    crate::leanh::lean_dec(v___x_2960_);
    v___x_2964_ = l_Std_Time_Duration_ofNanoseconds(v___x_2963_);
    crate::leanh::lean_dec(v___x_2963_);
    v___x_2965_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2964_);
    return v___x_2965_;
}
pub unsafe fn l_Std_Time_PlainDateTime_instHAddDuration___lam__0___boxed(
    mut v_x_2966_: *mut crate::leanh::LeanObject,
    mut v_y_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ = l_Std_Time_PlainDateTime_instHAddDuration___lam__0(v_x_2966_, v_y_2967_);
    crate::leanh::lean_dec_ref(v_y_2967_);
    return v_res_2968_;
}
pub unsafe fn l_Std_Time_PlainDate_atTime(
    mut v_date_2971_: *mut crate::leanh::LeanObject,
    mut v_time_2972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2973_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2973_, 0, v_date_2971_);
    crate::leanh::lean_ctor_set(v___x_2973_, 1, v_time_2972_);
    return v___x_2973_;
}
pub unsafe fn l_Std_Time_PlainTime_atDate(
    mut v_time_2974_: *mut crate::leanh::LeanObject,
    mut v_date_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2976_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2976_, 0, v_date_2975_);
    crate::leanh::lean_ctor_set(v___x_2976_, 1, v_time_2974_);
    return v___x_2976_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_DateTime_PlainDateTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_DateTime_WallTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Std_Time_instInhabitedPlainDateTime_default =
        _init_l_Std_Time_instInhabitedPlainDateTime_default();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedPlainDateTime_default);
    l_Std_Time_instInhabitedPlainDateTime = _init_l_Std_Time_instInhabitedPlainDateTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instInhabitedPlainDateTime);
    l_Std_Time_instOrdPlainDateTime = _init_l_Std_Time_instOrdPlainDateTime();
    crate::leanh::lean_mark_persistent(l_Std_Time_instOrdPlainDateTime);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_DateTime_PlainDateTime(
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
pub unsafe fn initialize_Std_Time_DateTime_PlainDateTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_DateTime_WallTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_DateTime_PlainDateTime(builtin);
}
