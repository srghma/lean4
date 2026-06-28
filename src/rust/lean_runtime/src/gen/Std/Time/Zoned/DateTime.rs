// Lean compiler output
// Module: Std.Time.Zoned.DateTime
// Imports: Std.Time.DateTime Std.Time.Zoned.TimeZone Std.Time.Date.Unit.Month Std.Time.Date.Unit.Year Std.Time.DateTime.PlainDateTime
use crate::r#gen::Init::Data::Ord::Basic::l_compareOn___boxed;
use crate::r#gen::Std::Time::Date::PlainDate::{
    l_Std_Time_PlainDate_addMonthsClip, l_Std_Time_PlainDate_addMonthsRollOver,
    l_Std_Time_PlainDate_alignedWeekOfMonth, l_Std_Time_PlainDate_ofEpochDay,
    l_Std_Time_PlainDate_quarter, l_Std_Time_PlainDate_rollOver, l_Std_Time_PlainDate_toEpochDay,
    l_Std_Time_PlainDate_weekOfYear, l_Std_Time_PlainDate_weekYear, l_Std_Time_PlainDate_weekday,
};
use crate::r#gen::Std::Time::Date::Unit::Month::{
    initialize_Std_Time_Date_Unit_Month, l_Std_Time_Month_Ordinal_days,
    runtime_initialize_Std_Time_Date_Unit_Month,
};
use crate::r#gen::Std::Time::Date::Unit::Year::{
    initialize_Std_Time_Date_Unit_Year, l_Std_Time_Year_Offset_era,
    runtime_initialize_Std_Time_Date_Unit_Year,
};
use crate::r#gen::Std::Time::Date::ValidDate::l_Std_Time_ValidDate_dayOfYear;
use crate::r#gen::Std::Time::DateTime::PlainDateTime::{
    initialize_Std_Time_DateTime_PlainDateTime, l_Std_Time_PlainDateTime_addMonthsClip,
    l_Std_Time_PlainDateTime_addMonthsRollOver, l_Std_Time_PlainDateTime_ofWallTime,
    l_Std_Time_PlainDateTime_toWallTime, l_Std_Time_PlainDateTime_weekOfMonth,
    l_Std_Time_PlainDateTime_withWeekday, runtime_initialize_Std_Time_DateTime_PlainDateTime,
};
use crate::r#gen::Std::Time::DateTime::Timestamp::{
    l_Std_Time_instInhabitedTimestamp_default, l_Std_Time_instOrdTimestamp,
};
use crate::r#gen::Std::Time::DateTime::{
    initialize_Std_Time_DateTime, runtime_initialize_Std_Time_DateTime,
};
use crate::r#gen::Std::Time::Duration::{
    l_Std_Time_Duration_ofNanoseconds, l_Std_Time_instDecidableEqDuration_decEq,
};
use crate::r#gen::Std::Time::Zoned::TimeZone::{
    initialize_Std_Time_Zoned_TimeZone, runtime_initialize_Std_Time_Zoned_TimeZone,
};
use crate::lean_imports_rs::Init::Core::{lean_mk_thunk, lean_thunk_get_own};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_mul, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_emod, lean_int_mod};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Std_Time_instBEqDateTime___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_instBEqDateTime___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instBEqDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instBEqDateTime___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_instOrdDateTime___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_instOrdDateTime___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_instOrdDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDateTime___closed__0_value) as *mut LeanObject;
static mut l_Std_Time_instOrdDateTime___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_instOrdDateTime___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_ofPlainDateTime___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_ofPlainDateTime___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_addHours___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_addHours___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_addMinutes___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_addMinutes___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_addMilliseconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_addMilliseconds___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_addDays___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_addDays___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_addWeeks___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_addWeeks___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_addYearsRollOver___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_addYearsRollOver___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_withDaysClip___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_withDaysClip___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_withDaysClip___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_withDaysClip___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_withDaysClip___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_withDaysClip___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_DateTime_withMilliseconds___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_DateTime_withMilliseconds___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_DateTime_instHSubDuration___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Std_Time_DateTime_instHSubDuration___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_DateTime_instHSubDuration___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateTime_instHSubDuration___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Std_Time_instBEqDateTime___lam__0(
    mut v_x_2178_: *mut LeanObject,
    mut v_y_2179_: *mut LeanObject,
) -> u8 {
    let mut v_timestamp_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_timestamp_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    v_timestamp_2180_ = lean_ctor_get(v_x_2178_, 0);
    v_timestamp_2181_ = lean_ctor_get(v_y_2179_, 0);
    v___x_2182_ = l_Std_Time_instDecidableEqDuration_decEq(v_timestamp_2180_, v_timestamp_2181_);
    return v___x_2182_;
}
pub unsafe fn l_Std_Time_instBEqDateTime___lam__0___boxed(
    mut v_x_2183_: *mut LeanObject,
    mut v_y_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2185_: u8 = 0;
    let mut v_r_2186_: *mut LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Std_Time_instBEqDateTime___lam__0(v_x_2183_, v_y_2184_);
    lean_dec_ref(v_y_2184_);
    lean_dec_ref(v_x_2183_);
    v_r_2186_ = lean_box((v_res_2185_) as usize);
    return v_r_2186_;
}
pub unsafe fn l_Std_Time_instBEqDateTime(mut v_tz_2188_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_2189_: *mut LeanObject = core::ptr::null_mut();
    v___f_2189_ = l_Std_Time_instBEqDateTime___closed__0;
    return v___f_2189_;
}
pub unsafe fn l_Std_Time_instBEqDateTime___boxed(
    mut v_tz_2190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2191_: *mut LeanObject = core::ptr::null_mut();
    v_res_2191_ = l_Std_Time_instBEqDateTime(v_tz_2190_);
    lean_dec_ref(v_tz_2190_);
    return v_res_2191_;
}
pub unsafe fn l_Std_Time_instOrdDateTime___lam__0(
    mut v_x_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2193_: *mut LeanObject = core::ptr::null_mut();
    v_timestamp_2193_ = lean_ctor_get(v_x_2192_, 0);
    lean_inc_ref(v_timestamp_2193_);
    return v_timestamp_2193_;
}
pub unsafe fn l_Std_Time_instOrdDateTime___lam__0___boxed(
    mut v_x_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2195_: *mut LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Time_instOrdDateTime___lam__0(v_x_2194_);
    lean_dec_ref(v_x_2194_);
    return v_res_2195_;
}
pub unsafe fn _init_l_Std_Time_instOrdDateTime___closed__1() -> *mut LeanObject {
    let mut v___f_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    v___f_2197_ = l_Std_Time_instOrdDateTime___closed__0;
    v___x_2198_ = l_Std_Time_instOrdTimestamp;
    v___x_2199_ = lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_2199_, 0, lean_box(0));
    lean_closure_set(v___x_2199_, 1, lean_box(0));
    lean_closure_set(v___x_2199_, 2, v___x_2198_);
    lean_closure_set(v___x_2199_, 3, v___f_2197_);
    return v___x_2199_;
}
pub unsafe fn l_Std_Time_instOrdDateTime(mut v_tz_2200_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    v___x_2201_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdDateTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdDateTime___closed__1_once),
        _init_l_Std_Time_instOrdDateTime___closed__1,
    );
    return v___x_2201_;
}
pub unsafe fn l_Std_Time_instOrdDateTime___boxed(
    mut v_tz_2202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2203_: *mut LeanObject = core::ptr::null_mut();
    v_res_2203_ = l_Std_Time_instOrdDateTime(v_tz_2202_);
    lean_dec_ref(v_tz_2202_);
    return v_res_2203_;
}
pub unsafe fn _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0() -> *mut LeanObject {
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    v___x_2204_ = lean_unsigned_to_nat(0);
    v___x_2205_ = lean_nat_to_int(v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    v___x_2206_ = lean_unsigned_to_nat(1000000000);
    v___x_2207_ = lean_nat_to_int(v___x_2206_);
    return v___x_2207_;
}
pub unsafe fn l_Std_Time_DateTime_ofTimestamp___lam__0(
    mut v_tz_2208_: *mut LeanObject,
    mut v_tm_2209_: *mut LeanObject,
    mut v_x_2210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2211_ = lean_ctor_get(v_tz_2208_, 0);
    v_second_2212_ = lean_ctor_get(v_tm_2209_, 0);
    v_nano_2213_ = lean_ctor_get(v_tm_2209_, 1);
    v___x_2214_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2215_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2216_ = lean_int_mul(v_second_2212_, v___x_2215_);
    v___x_2217_ = lean_int_add(v___x_2216_, v_nano_2213_);
    lean_dec(v___x_2216_);
    v___x_2218_ = lean_int_mul(v_offset_2211_, v___x_2215_);
    v___x_2219_ = lean_int_add(v___x_2218_, v___x_2214_);
    lean_dec(v___x_2218_);
    v___x_2220_ = lean_int_add(v___x_2217_, v___x_2219_);
    lean_dec(v___x_2219_);
    lean_dec(v___x_2217_);
    v___x_2221_ = l_Std_Time_Duration_ofNanoseconds(v___x_2220_);
    lean_dec(v___x_2220_);
    v___x_2222_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2221_);
    return v___x_2222_;
}
pub unsafe fn l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(
    mut v_tz_2223_: *mut LeanObject,
    mut v_tm_2224_: *mut LeanObject,
    mut v_x_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2226_: *mut LeanObject = core::ptr::null_mut();
    v_res_2226_ = l_Std_Time_DateTime_ofTimestamp___lam__0(v_tz_2223_, v_tm_2224_, v_x_2225_);
    lean_dec_ref(v_tm_2224_);
    lean_dec_ref(v_tz_2223_);
    return v_res_2226_;
}
pub unsafe fn l_Std_Time_DateTime_ofTimestamp(
    mut v_tm_2227_: *mut LeanObject,
    mut v_tz_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_tm_2227_);
    v___f_2229_ = lean_alloc_closure(
        l_Std_Time_DateTime_ofTimestamp___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2229_, 0, v_tz_2228_);
    lean_closure_set(v___f_2229_, 1, v_tm_2227_);
    v___x_2230_ = lean_mk_thunk(v___f_2229_);
    v___x_2231_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2231_, 0, v_tm_2227_);
    lean_ctor_set(v___x_2231_, 1, v___x_2230_);
    return v___x_2231_;
}
pub unsafe fn l_Std_Time_DateTime_instInhabited___lam__0(
    mut v_tz_2232_: *mut LeanObject,
    mut v___x_2233_: *mut LeanObject,
    mut v_x_2234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2235_ = lean_ctor_get(v_tz_2232_, 0);
    v_second_2236_ = lean_ctor_get(v___x_2233_, 0);
    v_nano_2237_ = lean_ctor_get(v___x_2233_, 1);
    v___x_2238_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2239_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2240_ = lean_int_mul(v_second_2236_, v___x_2239_);
    v___x_2241_ = lean_int_add(v___x_2240_, v_nano_2237_);
    lean_dec(v___x_2240_);
    v___x_2242_ = lean_int_mul(v_offset_2235_, v___x_2239_);
    v___x_2243_ = lean_int_add(v___x_2242_, v___x_2238_);
    lean_dec(v___x_2242_);
    v___x_2244_ = lean_int_add(v___x_2241_, v___x_2243_);
    lean_dec(v___x_2243_);
    lean_dec(v___x_2241_);
    v___x_2245_ = l_Std_Time_Duration_ofNanoseconds(v___x_2244_);
    lean_dec(v___x_2244_);
    v___x_2246_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2245_);
    return v___x_2246_;
}
pub unsafe fn l_Std_Time_DateTime_instInhabited___lam__0___boxed(
    mut v_tz_2247_: *mut LeanObject,
    mut v___x_2248_: *mut LeanObject,
    mut v_x_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ = l_Std_Time_DateTime_instInhabited___lam__0(v_tz_2247_, v___x_2248_, v_x_2249_);
    lean_dec_ref(v___x_2248_);
    lean_dec_ref(v_tz_2247_);
    return v_res_2250_;
}
pub unsafe fn l_Std_Time_DateTime_instInhabited(
    mut v_tz_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    v___x_2252_ = l_Std_Time_instInhabitedTimestamp_default;
    v___f_2253_ = lean_alloc_closure(
        l_Std_Time_DateTime_instInhabited___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2253_, 0, v_tz_2251_);
    lean_closure_set(v___f_2253_, 1, v___x_2252_);
    v___x_2254_ = lean_mk_thunk(v___f_2253_);
    v___x_2255_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2255_, 0, v___x_2252_);
    lean_ctor_set(v___x_2255_, 1, v___x_2254_);
    return v___x_2255_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay___redArg(
    mut v_date_2256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    v_date_2257_ = lean_ctor_get(v_date_2256_, 1);
    v___x_2258_ = lean_thunk_get_own(v_date_2257_);
    v_date_2259_ = lean_ctor_get(v___x_2258_, 0);
    lean_inc_ref(v_date_2259_);
    lean_dec(v___x_2258_);
    v___x_2260_ = l_Std_Time_PlainDate_toEpochDay(v_date_2259_);
    return v___x_2260_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay___redArg___boxed(
    mut v_date_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2262_: *mut LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Std_Time_DateTime_toEpochDay___redArg(v_date_2261_);
    lean_dec_ref(v_date_2261_);
    return v_res_2262_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay(
    mut v_tz_2263_: *mut LeanObject,
    mut v_date_2264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2265_: *mut LeanObject = core::ptr::null_mut();
    v___x_2265_ = l_Std_Time_DateTime_toEpochDay___redArg(v_date_2264_);
    return v___x_2265_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay___boxed(
    mut v_tz_2266_: *mut LeanObject,
    mut v_date_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2268_: *mut LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Std_Time_DateTime_toEpochDay(v_tz_2266_, v_date_2267_);
    lean_dec_ref(v_date_2267_);
    lean_dec_ref(v_tz_2266_);
    return v_res_2268_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp___redArg(
    mut v_date_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2270_: *mut LeanObject = core::ptr::null_mut();
    v_timestamp_2270_ = lean_ctor_get(v_date_2269_, 0);
    lean_inc_ref(v_timestamp_2270_);
    return v_timestamp_2270_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp___redArg___boxed(
    mut v_date_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2272_: *mut LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Std_Time_DateTime_toTimestamp___redArg(v_date_2271_);
    lean_dec_ref(v_date_2271_);
    return v_res_2272_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp(
    mut v_tz_2273_: *mut LeanObject,
    mut v_date_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2275_: *mut LeanObject = core::ptr::null_mut();
    v_timestamp_2275_ = lean_ctor_get(v_date_2274_, 0);
    lean_inc_ref(v_timestamp_2275_);
    return v_timestamp_2275_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp___boxed(
    mut v_tz_2276_: *mut LeanObject,
    mut v_date_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2278_: *mut LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Std_Time_DateTime_toTimestamp(v_tz_2276_, v_date_2277_);
    lean_dec_ref(v_date_2277_);
    lean_dec_ref(v_tz_2276_);
    return v_res_2278_;
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(
    mut v_tz_u2081_2279_: *mut LeanObject,
    mut v_timestamp_2280_: *mut LeanObject,
    mut v_x_2281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2282_ = lean_ctor_get(v_tz_u2081_2279_, 0);
    v_second_2283_ = lean_ctor_get(v_timestamp_2280_, 0);
    v_nano_2284_ = lean_ctor_get(v_timestamp_2280_, 1);
    v___x_2285_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2286_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2287_ = lean_int_mul(v_second_2283_, v___x_2286_);
    v___x_2288_ = lean_int_add(v___x_2287_, v_nano_2284_);
    lean_dec(v___x_2287_);
    v___x_2289_ = lean_int_mul(v_offset_2282_, v___x_2286_);
    v___x_2290_ = lean_int_add(v___x_2289_, v___x_2285_);
    lean_dec(v___x_2289_);
    v___x_2291_ = lean_int_add(v___x_2288_, v___x_2290_);
    lean_dec(v___x_2290_);
    lean_dec(v___x_2288_);
    v___x_2292_ = l_Std_Time_Duration_ofNanoseconds(v___x_2291_);
    lean_dec(v___x_2291_);
    v___x_2293_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(
    mut v_tz_u2081_2294_: *mut LeanObject,
    mut v_timestamp_2295_: *mut LeanObject,
    mut v_x_2296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2297_: *mut LeanObject = core::ptr::null_mut();
    v_res_2297_ = l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(
        v_tz_u2081_2294_,
        v_timestamp_2295_,
        v_x_2296_,
    );
    lean_dec_ref(v_timestamp_2295_);
    lean_dec_ref(v_tz_u2081_2294_);
    return v_res_2297_;
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone___redArg(
    mut v_date_2298_: *mut LeanObject,
    mut v_tz_u2081_2299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___f_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v_unused_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2300_ = lean_ctor_get(v_date_2298_, 0);
                v_isSharedCheck_2309_ = (!lean_is_exclusive(v_date_2298_)) as u8;
                if v_isSharedCheck_2309_ == 0 {
                    v_unused_2310_ = lean_ctor_get(v_date_2298_, 1);
                    lean_dec(v_unused_2310_);
                    v___x_2302_ = v_date_2298_;
                    v_isShared_2303_ = v_isSharedCheck_2309_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2300_);
                    lean_dec(v_date_2298_);
                    v___x_2302_ = lean_box(0);
                    v_isShared_2303_ = v_isSharedCheck_2309_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_timestamp_2300_);
                v___f_2304_ = lean_alloc_closure(
                    l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2304_, 0, v_tz_u2081_2299_);
                lean_closure_set(v___f_2304_, 1, v_timestamp_2300_);
                v___x_2305_ = lean_mk_thunk(v___f_2304_);
                if v_isShared_2303_ == 0 {
                    lean_ctor_set(v___x_2302_, 1, v___x_2305_);
                    v___x_2307_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_timestamp_2300_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2305_);
                    v___x_2307_ = v_reuseFailAlloc_2308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone(
    mut v_tz_2311_: *mut LeanObject,
    mut v_date_2312_: *mut LeanObject,
    mut v_tz_u2081_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___f_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_unused_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2314_ = lean_ctor_get(v_date_2312_, 0);
                v_isSharedCheck_2323_ = (!lean_is_exclusive(v_date_2312_)) as u8;
                if v_isSharedCheck_2323_ == 0 {
                    v_unused_2324_ = lean_ctor_get(v_date_2312_, 1);
                    lean_dec(v_unused_2324_);
                    v___x_2316_ = v_date_2312_;
                    v_isShared_2317_ = v_isSharedCheck_2323_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2314_);
                    lean_dec(v_date_2312_);
                    v___x_2316_ = lean_box(0);
                    v_isShared_2317_ = v_isSharedCheck_2323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_timestamp_2314_);
                v___f_2318_ = lean_alloc_closure(
                    l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2318_, 0, v_tz_u2081_2313_);
                lean_closure_set(v___f_2318_, 1, v_timestamp_2314_);
                v___x_2319_ = lean_mk_thunk(v___f_2318_);
                if v_isShared_2317_ == 0 {
                    lean_ctor_set(v___x_2316_, 1, v___x_2319_);
                    v___x_2321_ = v___x_2316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_timestamp_2314_);
                    lean_ctor_set(v_reuseFailAlloc_2322_, 1, v___x_2319_);
                    v___x_2321_ = v_reuseFailAlloc_2322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone___boxed(
    mut v_tz_2325_: *mut LeanObject,
    mut v_date_2326_: *mut LeanObject,
    mut v_tz_u2081_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Std_Time_DateTime_convertTimeZone(v_tz_2325_, v_date_2326_, v_tz_u2081_2327_);
    lean_dec_ref(v_tz_2325_);
    return v_res_2328_;
}
pub unsafe fn l_Std_Time_DateTime_ofPlainDateTime___lam__0(
    mut v_date_2329_: *mut LeanObject,
    mut v_x_2330_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_date_2329_);
    return v_date_2329_;
}
pub unsafe fn l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(
    mut v_date_2331_: *mut LeanObject,
    mut v_x_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2333_: *mut LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Std_Time_DateTime_ofPlainDateTime___lam__0(v_date_2331_, v_x_2332_);
    lean_dec_ref(v_date_2331_);
    return v_res_2333_;
}
pub unsafe fn _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0() -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v___x_2334_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2335_ = lean_int_neg(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn l_Std_Time_DateTime_ofPlainDateTime(
    mut v_date_2336_: *mut LeanObject,
    mut v_tz_2337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___f_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_2338_ = lean_ctor_get(v_tz_2337_, 0);
                lean_inc_ref(v_date_2336_);
                v___x_2339_ = l_Std_Time_PlainDateTime_toWallTime(v_date_2336_);
                v_second_2340_ = lean_ctor_get(v___x_2339_, 0);
                v_nano_2341_ = lean_ctor_get(v___x_2339_, 1);
                v_isSharedCheck_2359_ = (!lean_is_exclusive(v___x_2339_)) as u8;
                if v_isSharedCheck_2359_ == 0 {
                    v___x_2343_ = v___x_2339_;
                    v_isShared_2344_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nano_2341_);
                    lean_inc(v_second_2340_);
                    lean_dec(v___x_2339_);
                    v___x_2343_ = lean_box(0);
                    v_isShared_2344_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2345_ = lean_alloc_closure(
                    l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2345_, 0, v_date_2336_);
                v___x_2346_ = lean_int_neg(v_offset_2338_);
                v___x_2347_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2348_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2349_ = lean_int_mul(v_second_2340_, v___x_2348_);
                lean_dec(v_second_2340_);
                v___x_2350_ = lean_int_add(v___x_2349_, v_nano_2341_);
                lean_dec(v_nano_2341_);
                lean_dec(v___x_2349_);
                v___x_2351_ = lean_int_mul(v___x_2346_, v___x_2348_);
                lean_dec(v___x_2346_);
                v___x_2352_ = lean_int_add(v___x_2351_, v___x_2347_);
                lean_dec(v___x_2351_);
                v___x_2353_ = lean_int_add(v___x_2350_, v___x_2352_);
                lean_dec(v___x_2352_);
                lean_dec(v___x_2350_);
                v_tm_2354_ = l_Std_Time_Duration_ofNanoseconds(v___x_2353_);
                lean_dec(v___x_2353_);
                v___x_2355_ = lean_mk_thunk(v___f_2345_);
                if v_isShared_2344_ == 0 {
                    lean_ctor_set(v___x_2343_, 1, v___x_2355_);
                    lean_ctor_set(v___x_2343_, 0, v_tm_2354_);
                    v___x_2357_ = v___x_2343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_tm_2354_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2355_);
                    v___x_2357_ = v_reuseFailAlloc_2358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_ofPlainDateTime___boxed(
    mut v_date_2360_: *mut LeanObject,
    mut v_tz_2361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2362_: *mut LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Std_Time_DateTime_ofPlainDateTime(v_date_2360_, v_tz_2361_);
    lean_dec_ref(v_tz_2361_);
    return v_res_2362_;
}
pub unsafe fn l_Std_Time_DateTime_addHours___lam__0(
    mut v_tz_2363_: *mut LeanObject,
    mut v___x_2364_: *mut LeanObject,
    mut v___x_2365_: *mut LeanObject,
    mut v___x_2366_: *mut LeanObject,
    mut v_x_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2368_ = lean_ctor_get(v_tz_2363_, 0);
    v_second_2369_ = lean_ctor_get(v___x_2364_, 0);
    v_nano_2370_ = lean_ctor_get(v___x_2364_, 1);
    v___x_2371_ = lean_int_mul(v_second_2369_, v___x_2365_);
    v___x_2372_ = lean_int_add(v___x_2371_, v_nano_2370_);
    lean_dec(v___x_2371_);
    v___x_2373_ = lean_int_mul(v_offset_2368_, v___x_2365_);
    v___x_2374_ = lean_int_add(v___x_2373_, v___x_2366_);
    lean_dec(v___x_2373_);
    v___x_2375_ = lean_int_add(v___x_2372_, v___x_2374_);
    lean_dec(v___x_2374_);
    lean_dec(v___x_2372_);
    v___x_2376_ = l_Std_Time_Duration_ofNanoseconds(v___x_2375_);
    lean_dec(v___x_2375_);
    v___x_2377_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2376_);
    return v___x_2377_;
}
pub unsafe fn l_Std_Time_DateTime_addHours___lam__0___boxed(
    mut v_tz_2378_: *mut LeanObject,
    mut v___x_2379_: *mut LeanObject,
    mut v___x_2380_: *mut LeanObject,
    mut v___x_2381_: *mut LeanObject,
    mut v_x_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2383_: *mut LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Std_Time_DateTime_addHours___lam__0(
        v_tz_2378_,
        v___x_2379_,
        v___x_2380_,
        v___x_2381_,
        v_x_2382_,
    );
    lean_dec(v___x_2381_);
    lean_dec(v___x_2380_);
    lean_dec_ref(v___x_2379_);
    lean_dec_ref(v_tz_2378_);
    return v_res_2383_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addHours___closed__0() -> *mut LeanObject {
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    v___x_2384_ = lean_unsigned_to_nat(3600);
    v___x_2385_ = lean_nat_to_int(v___x_2384_);
    return v___x_2385_;
}
pub unsafe fn l_Std_Time_DateTime_addHours(
    mut v_tz_2386_: *mut LeanObject,
    mut v_dt_2387_: *mut LeanObject,
    mut v_hours_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v_second_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_unused_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2389_ = lean_ctor_get(v_dt_2387_, 0);
                v_isSharedCheck_2410_ = (!lean_is_exclusive(v_dt_2387_)) as u8;
                if v_isSharedCheck_2410_ == 0 {
                    v_unused_2411_ = lean_ctor_get(v_dt_2387_, 1);
                    lean_dec(v_unused_2411_);
                    v___x_2391_ = v_dt_2387_;
                    v_isShared_2392_ = v_isSharedCheck_2410_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2389_);
                    lean_dec(v_dt_2387_);
                    v___x_2391_ = lean_box(0);
                    v_isShared_2392_ = v_isSharedCheck_2410_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2393_ = lean_ctor_get(v_timestamp_2389_, 0);
                lean_inc(v_second_2393_);
                v_nano_2394_ = lean_ctor_get(v_timestamp_2389_, 1);
                lean_inc(v_nano_2394_);
                lean_dec_ref(v_timestamp_2389_);
                v___x_2395_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0_once),
                    _init_l_Std_Time_DateTime_addHours___closed__0,
                );
                v___x_2396_ = lean_int_mul(v_hours_2388_, v___x_2395_);
                v___x_2397_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2398_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2399_ = lean_int_mul(v_second_2393_, v___x_2398_);
                lean_dec(v_second_2393_);
                v___x_2400_ = lean_int_add(v___x_2399_, v_nano_2394_);
                lean_dec(v_nano_2394_);
                lean_dec(v___x_2399_);
                v___x_2401_ = lean_int_mul(v___x_2396_, v___x_2398_);
                lean_dec(v___x_2396_);
                v___x_2402_ = lean_int_add(v___x_2401_, v___x_2397_);
                lean_dec(v___x_2401_);
                v___x_2403_ = lean_int_add(v___x_2400_, v___x_2402_);
                lean_dec(v___x_2402_);
                lean_dec(v___x_2400_);
                v___x_2404_ = l_Std_Time_Duration_ofNanoseconds(v___x_2403_);
                lean_dec(v___x_2403_);
                lean_inc_ref(v___x_2404_);
                v___f_2405_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2405_, 0, v_tz_2386_);
                lean_closure_set(v___f_2405_, 1, v___x_2404_);
                lean_closure_set(v___f_2405_, 2, v___x_2398_);
                lean_closure_set(v___f_2405_, 3, v___x_2397_);
                v___x_2406_ = lean_mk_thunk(v___f_2405_);
                if v_isShared_2392_ == 0 {
                    lean_ctor_set(v___x_2391_, 1, v___x_2406_);
                    lean_ctor_set(v___x_2391_, 0, v___x_2404_);
                    v___x_2408_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2404_);
                    lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2406_);
                    v___x_2408_ = v_reuseFailAlloc_2409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addHours___boxed(
    mut v_tz_2412_: *mut LeanObject,
    mut v_dt_2413_: *mut LeanObject,
    mut v_hours_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2415_: *mut LeanObject = core::ptr::null_mut();
    v_res_2415_ = l_Std_Time_DateTime_addHours(v_tz_2412_, v_dt_2413_, v_hours_2414_);
    lean_dec(v_hours_2414_);
    return v_res_2415_;
}
pub unsafe fn l_Std_Time_DateTime_subHours(
    mut v_tz_2416_: *mut LeanObject,
    mut v_dt_2417_: *mut LeanObject,
    mut v_hours_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v_second_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut v_unused_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2419_ = lean_ctor_get(v_dt_2417_, 0);
                v_isSharedCheck_2442_ = (!lean_is_exclusive(v_dt_2417_)) as u8;
                if v_isSharedCheck_2442_ == 0 {
                    v_unused_2443_ = lean_ctor_get(v_dt_2417_, 1);
                    lean_dec(v_unused_2443_);
                    v___x_2421_ = v_dt_2417_;
                    v_isShared_2422_ = v_isSharedCheck_2442_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2419_);
                    lean_dec(v_dt_2417_);
                    v___x_2421_ = lean_box(0);
                    v_isShared_2422_ = v_isSharedCheck_2442_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2423_ = lean_ctor_get(v_timestamp_2419_, 0);
                lean_inc(v_second_2423_);
                v_nano_2424_ = lean_ctor_get(v_timestamp_2419_, 1);
                lean_inc(v_nano_2424_);
                lean_dec_ref(v_timestamp_2419_);
                v___x_2425_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0_once),
                    _init_l_Std_Time_DateTime_addHours___closed__0,
                );
                v___x_2426_ = lean_int_mul(v_hours_2418_, v___x_2425_);
                v___x_2427_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2428_ = lean_int_neg(v___x_2426_);
                lean_dec(v___x_2426_);
                v___x_2429_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2430_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2431_ = lean_int_mul(v_second_2423_, v___x_2430_);
                lean_dec(v_second_2423_);
                v___x_2432_ = lean_int_add(v___x_2431_, v_nano_2424_);
                lean_dec(v_nano_2424_);
                lean_dec(v___x_2431_);
                v___x_2433_ = lean_int_mul(v___x_2428_, v___x_2430_);
                lean_dec(v___x_2428_);
                v___x_2434_ = lean_int_add(v___x_2433_, v___x_2429_);
                lean_dec(v___x_2433_);
                v___x_2435_ = lean_int_add(v___x_2432_, v___x_2434_);
                lean_dec(v___x_2434_);
                lean_dec(v___x_2432_);
                v___x_2436_ = l_Std_Time_Duration_ofNanoseconds(v___x_2435_);
                lean_dec(v___x_2435_);
                lean_inc_ref(v___x_2436_);
                v___f_2437_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2437_, 0, v_tz_2416_);
                lean_closure_set(v___f_2437_, 1, v___x_2436_);
                lean_closure_set(v___f_2437_, 2, v___x_2430_);
                lean_closure_set(v___f_2437_, 3, v___x_2427_);
                v___x_2438_ = lean_mk_thunk(v___f_2437_);
                if v_isShared_2422_ == 0 {
                    lean_ctor_set(v___x_2421_, 1, v___x_2438_);
                    lean_ctor_set(v___x_2421_, 0, v___x_2436_);
                    v___x_2440_ = v___x_2421_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2436_);
                    lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2438_);
                    v___x_2440_ = v_reuseFailAlloc_2441_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2440_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subHours___boxed(
    mut v_tz_2444_: *mut LeanObject,
    mut v_dt_2445_: *mut LeanObject,
    mut v_hours_2446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2447_: *mut LeanObject = core::ptr::null_mut();
    v_res_2447_ = l_Std_Time_DateTime_subHours(v_tz_2444_, v_dt_2445_, v_hours_2446_);
    lean_dec(v_hours_2446_);
    return v_res_2447_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addMinutes___closed__0() -> *mut LeanObject {
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    v___x_2448_ = lean_unsigned_to_nat(60);
    v___x_2449_ = lean_nat_to_int(v___x_2448_);
    return v___x_2449_;
}
pub unsafe fn l_Std_Time_DateTime_addMinutes(
    mut v_tz_2450_: *mut LeanObject,
    mut v_dt_2451_: *mut LeanObject,
    mut v_minutes_2452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v_second_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut v_unused_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2453_ = lean_ctor_get(v_dt_2451_, 0);
                v_isSharedCheck_2474_ = (!lean_is_exclusive(v_dt_2451_)) as u8;
                if v_isSharedCheck_2474_ == 0 {
                    v_unused_2475_ = lean_ctor_get(v_dt_2451_, 1);
                    lean_dec(v_unused_2475_);
                    v___x_2455_ = v_dt_2451_;
                    v_isShared_2456_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2453_);
                    lean_dec(v_dt_2451_);
                    v___x_2455_ = lean_box(0);
                    v_isShared_2456_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2457_ = lean_ctor_get(v_timestamp_2453_, 0);
                lean_inc(v_second_2457_);
                v_nano_2458_ = lean_ctor_get(v_timestamp_2453_, 1);
                lean_inc(v_nano_2458_);
                lean_dec_ref(v_timestamp_2453_);
                v___x_2459_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_DateTime_addMinutes___closed__0,
                );
                v___x_2460_ = lean_int_mul(v_minutes_2452_, v___x_2459_);
                v___x_2461_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2462_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2463_ = lean_int_mul(v_second_2457_, v___x_2462_);
                lean_dec(v_second_2457_);
                v___x_2464_ = lean_int_add(v___x_2463_, v_nano_2458_);
                lean_dec(v_nano_2458_);
                lean_dec(v___x_2463_);
                v___x_2465_ = lean_int_mul(v___x_2460_, v___x_2462_);
                lean_dec(v___x_2460_);
                v___x_2466_ = lean_int_add(v___x_2465_, v___x_2461_);
                lean_dec(v___x_2465_);
                v___x_2467_ = lean_int_add(v___x_2464_, v___x_2466_);
                lean_dec(v___x_2466_);
                lean_dec(v___x_2464_);
                v___x_2468_ = l_Std_Time_Duration_ofNanoseconds(v___x_2467_);
                lean_dec(v___x_2467_);
                lean_inc_ref(v___x_2468_);
                v___f_2469_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2469_, 0, v_tz_2450_);
                lean_closure_set(v___f_2469_, 1, v___x_2468_);
                lean_closure_set(v___f_2469_, 2, v___x_2462_);
                lean_closure_set(v___f_2469_, 3, v___x_2461_);
                v___x_2470_ = lean_mk_thunk(v___f_2469_);
                if v_isShared_2456_ == 0 {
                    lean_ctor_set(v___x_2455_, 1, v___x_2470_);
                    lean_ctor_set(v___x_2455_, 0, v___x_2468_);
                    v___x_2472_ = v___x_2455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2468_);
                    lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2470_);
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
pub unsafe fn l_Std_Time_DateTime_addMinutes___boxed(
    mut v_tz_2476_: *mut LeanObject,
    mut v_dt_2477_: *mut LeanObject,
    mut v_minutes_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2479_: *mut LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_Std_Time_DateTime_addMinutes(v_tz_2476_, v_dt_2477_, v_minutes_2478_);
    lean_dec(v_minutes_2478_);
    return v_res_2479_;
}
pub unsafe fn l_Std_Time_DateTime_subMinutes(
    mut v_tz_2480_: *mut LeanObject,
    mut v_dt_2481_: *mut LeanObject,
    mut v_minutes_2482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v_second_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut v_unused_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2483_ = lean_ctor_get(v_dt_2481_, 0);
                v_isSharedCheck_2506_ = (!lean_is_exclusive(v_dt_2481_)) as u8;
                if v_isSharedCheck_2506_ == 0 {
                    v_unused_2507_ = lean_ctor_get(v_dt_2481_, 1);
                    lean_dec(v_unused_2507_);
                    v___x_2485_ = v_dt_2481_;
                    v_isShared_2486_ = v_isSharedCheck_2506_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2483_);
                    lean_dec(v_dt_2481_);
                    v___x_2485_ = lean_box(0);
                    v_isShared_2486_ = v_isSharedCheck_2506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2487_ = lean_ctor_get(v_timestamp_2483_, 0);
                lean_inc(v_second_2487_);
                v_nano_2488_ = lean_ctor_get(v_timestamp_2483_, 1);
                lean_inc(v_nano_2488_);
                lean_dec_ref(v_timestamp_2483_);
                v___x_2489_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_DateTime_addMinutes___closed__0,
                );
                v___x_2490_ = lean_int_mul(v_minutes_2482_, v___x_2489_);
                v___x_2491_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2492_ = lean_int_neg(v___x_2490_);
                lean_dec(v___x_2490_);
                v___x_2493_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2494_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2495_ = lean_int_mul(v_second_2487_, v___x_2494_);
                lean_dec(v_second_2487_);
                v___x_2496_ = lean_int_add(v___x_2495_, v_nano_2488_);
                lean_dec(v_nano_2488_);
                lean_dec(v___x_2495_);
                v___x_2497_ = lean_int_mul(v___x_2492_, v___x_2494_);
                lean_dec(v___x_2492_);
                v___x_2498_ = lean_int_add(v___x_2497_, v___x_2493_);
                lean_dec(v___x_2497_);
                v___x_2499_ = lean_int_add(v___x_2496_, v___x_2498_);
                lean_dec(v___x_2498_);
                lean_dec(v___x_2496_);
                v___x_2500_ = l_Std_Time_Duration_ofNanoseconds(v___x_2499_);
                lean_dec(v___x_2499_);
                lean_inc_ref(v___x_2500_);
                v___f_2501_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2501_, 0, v_tz_2480_);
                lean_closure_set(v___f_2501_, 1, v___x_2500_);
                lean_closure_set(v___f_2501_, 2, v___x_2494_);
                lean_closure_set(v___f_2501_, 3, v___x_2491_);
                v___x_2502_ = lean_mk_thunk(v___f_2501_);
                if v_isShared_2486_ == 0 {
                    lean_ctor_set(v___x_2485_, 1, v___x_2502_);
                    lean_ctor_set(v___x_2485_, 0, v___x_2500_);
                    v___x_2504_ = v___x_2485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2500_);
                    lean_ctor_set(v_reuseFailAlloc_2505_, 1, v___x_2502_);
                    v___x_2504_ = v_reuseFailAlloc_2505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2504_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subMinutes___boxed(
    mut v_tz_2508_: *mut LeanObject,
    mut v_dt_2509_: *mut LeanObject,
    mut v_minutes_2510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2511_: *mut LeanObject = core::ptr::null_mut();
    v_res_2511_ = l_Std_Time_DateTime_subMinutes(v_tz_2508_, v_dt_2509_, v_minutes_2510_);
    lean_dec(v_minutes_2510_);
    return v_res_2511_;
}
pub unsafe fn l_Std_Time_DateTime_addSeconds(
    mut v_tz_2512_: *mut LeanObject,
    mut v_dt_2513_: *mut LeanObject,
    mut v_seconds_2514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v_second_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_unused_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2515_ = lean_ctor_get(v_dt_2513_, 0);
                v_isSharedCheck_2534_ = (!lean_is_exclusive(v_dt_2513_)) as u8;
                if v_isSharedCheck_2534_ == 0 {
                    v_unused_2535_ = lean_ctor_get(v_dt_2513_, 1);
                    lean_dec(v_unused_2535_);
                    v___x_2517_ = v_dt_2513_;
                    v_isShared_2518_ = v_isSharedCheck_2534_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2515_);
                    lean_dec(v_dt_2513_);
                    v___x_2517_ = lean_box(0);
                    v_isShared_2518_ = v_isSharedCheck_2534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2519_ = lean_ctor_get(v_timestamp_2515_, 0);
                lean_inc(v_second_2519_);
                v_nano_2520_ = lean_ctor_get(v_timestamp_2515_, 1);
                lean_inc(v_nano_2520_);
                lean_dec_ref(v_timestamp_2515_);
                v___x_2521_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2522_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2523_ = lean_int_mul(v_second_2519_, v___x_2522_);
                lean_dec(v_second_2519_);
                v___x_2524_ = lean_int_add(v___x_2523_, v_nano_2520_);
                lean_dec(v_nano_2520_);
                lean_dec(v___x_2523_);
                v___x_2525_ = lean_int_mul(v_seconds_2514_, v___x_2522_);
                v___x_2526_ = lean_int_add(v___x_2525_, v___x_2521_);
                lean_dec(v___x_2525_);
                v___x_2527_ = lean_int_add(v___x_2524_, v___x_2526_);
                lean_dec(v___x_2526_);
                lean_dec(v___x_2524_);
                v___x_2528_ = l_Std_Time_Duration_ofNanoseconds(v___x_2527_);
                lean_dec(v___x_2527_);
                lean_inc_ref(v___x_2528_);
                v___f_2529_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2529_, 0, v_tz_2512_);
                lean_closure_set(v___f_2529_, 1, v___x_2528_);
                lean_closure_set(v___f_2529_, 2, v___x_2522_);
                lean_closure_set(v___f_2529_, 3, v___x_2521_);
                v___x_2530_ = lean_mk_thunk(v___f_2529_);
                if v_isShared_2518_ == 0 {
                    lean_ctor_set(v___x_2517_, 1, v___x_2530_);
                    lean_ctor_set(v___x_2517_, 0, v___x_2528_);
                    v___x_2532_ = v___x_2517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2528_);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
                    v___x_2532_ = v_reuseFailAlloc_2533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2532_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addSeconds___boxed(
    mut v_tz_2536_: *mut LeanObject,
    mut v_dt_2537_: *mut LeanObject,
    mut v_seconds_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2539_: *mut LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std_Time_DateTime_addSeconds(v_tz_2536_, v_dt_2537_, v_seconds_2538_);
    lean_dec(v_seconds_2538_);
    return v_res_2539_;
}
pub unsafe fn l_Std_Time_DateTime_subSeconds(
    mut v_tz_2540_: *mut LeanObject,
    mut v_dt_2541_: *mut LeanObject,
    mut v_seconds_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v_second_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2543_ = lean_ctor_get(v_dt_2541_, 0);
                v_isSharedCheck_2564_ = (!lean_is_exclusive(v_dt_2541_)) as u8;
                if v_isSharedCheck_2564_ == 0 {
                    v_unused_2565_ = lean_ctor_get(v_dt_2541_, 1);
                    lean_dec(v_unused_2565_);
                    v___x_2545_ = v_dt_2541_;
                    v_isShared_2546_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2543_);
                    lean_dec(v_dt_2541_);
                    v___x_2545_ = lean_box(0);
                    v_isShared_2546_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2547_ = lean_ctor_get(v_timestamp_2543_, 0);
                lean_inc(v_second_2547_);
                v_nano_2548_ = lean_ctor_get(v_timestamp_2543_, 1);
                lean_inc(v_nano_2548_);
                lean_dec_ref(v_timestamp_2543_);
                v___x_2549_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2550_ = lean_int_neg(v_seconds_2542_);
                v___x_2551_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2552_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2553_ = lean_int_mul(v_second_2547_, v___x_2552_);
                lean_dec(v_second_2547_);
                v___x_2554_ = lean_int_add(v___x_2553_, v_nano_2548_);
                lean_dec(v_nano_2548_);
                lean_dec(v___x_2553_);
                v___x_2555_ = lean_int_mul(v___x_2550_, v___x_2552_);
                lean_dec(v___x_2550_);
                v___x_2556_ = lean_int_add(v___x_2555_, v___x_2551_);
                lean_dec(v___x_2555_);
                v___x_2557_ = lean_int_add(v___x_2554_, v___x_2556_);
                lean_dec(v___x_2556_);
                lean_dec(v___x_2554_);
                v___x_2558_ = l_Std_Time_Duration_ofNanoseconds(v___x_2557_);
                lean_dec(v___x_2557_);
                lean_inc_ref(v___x_2558_);
                v___f_2559_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2559_, 0, v_tz_2540_);
                lean_closure_set(v___f_2559_, 1, v___x_2558_);
                lean_closure_set(v___f_2559_, 2, v___x_2552_);
                lean_closure_set(v___f_2559_, 3, v___x_2549_);
                v___x_2560_ = lean_mk_thunk(v___f_2559_);
                if v_isShared_2546_ == 0 {
                    lean_ctor_set(v___x_2545_, 1, v___x_2560_);
                    lean_ctor_set(v___x_2545_, 0, v___x_2558_);
                    v___x_2562_ = v___x_2545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2563_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2558_);
                    lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2560_);
                    v___x_2562_ = v_reuseFailAlloc_2563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subSeconds___boxed(
    mut v_tz_2566_: *mut LeanObject,
    mut v_dt_2567_: *mut LeanObject,
    mut v_seconds_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2569_: *mut LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Std_Time_DateTime_subSeconds(v_tz_2566_, v_dt_2567_, v_seconds_2568_);
    lean_dec(v_seconds_2568_);
    return v_res_2569_;
}
pub unsafe fn l_Std_Time_DateTime_addMilliseconds___lam__0(
    mut v_tz_2570_: *mut LeanObject,
    mut v___x_2571_: *mut LeanObject,
    mut v___x_2572_: *mut LeanObject,
    mut v_x_2573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    v_offset_2574_ = lean_ctor_get(v_tz_2570_, 0);
    v_second_2575_ = lean_ctor_get(v___x_2571_, 0);
    v_nano_2576_ = lean_ctor_get(v___x_2571_, 1);
    v___x_2577_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2578_ = lean_int_mul(v_second_2575_, v___x_2572_);
    v___x_2579_ = lean_int_add(v___x_2578_, v_nano_2576_);
    lean_dec(v___x_2578_);
    v___x_2580_ = lean_int_mul(v_offset_2574_, v___x_2572_);
    v___x_2581_ = lean_int_add(v___x_2580_, v___x_2577_);
    lean_dec(v___x_2580_);
    v___x_2582_ = lean_int_add(v___x_2579_, v___x_2581_);
    lean_dec(v___x_2581_);
    lean_dec(v___x_2579_);
    v___x_2583_ = l_Std_Time_Duration_ofNanoseconds(v___x_2582_);
    lean_dec(v___x_2582_);
    v___x_2584_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2583_);
    return v___x_2584_;
}
pub unsafe fn l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(
    mut v_tz_2585_: *mut LeanObject,
    mut v___x_2586_: *mut LeanObject,
    mut v___x_2587_: *mut LeanObject,
    mut v_x_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2589_: *mut LeanObject = core::ptr::null_mut();
    v_res_2589_ = l_Std_Time_DateTime_addMilliseconds___lam__0(
        v_tz_2585_,
        v___x_2586_,
        v___x_2587_,
        v_x_2588_,
    );
    lean_dec(v___x_2587_);
    lean_dec_ref(v___x_2586_);
    lean_dec_ref(v_tz_2585_);
    return v_res_2589_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addMilliseconds___closed__0() -> *mut LeanObject {
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    v___x_2590_ = lean_unsigned_to_nat(1000000);
    v___x_2591_ = lean_nat_to_int(v___x_2590_);
    return v___x_2591_;
}
pub unsafe fn l_Std_Time_DateTime_addMilliseconds(
    mut v_tz_2592_: *mut LeanObject,
    mut v_dt_2593_: *mut LeanObject,
    mut v_milliseconds_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v_second_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut v_unused_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2595_ = lean_ctor_get(v_dt_2593_, 0);
                v_isSharedCheck_2618_ = (!lean_is_exclusive(v_dt_2593_)) as u8;
                if v_isSharedCheck_2618_ == 0 {
                    v_unused_2619_ = lean_ctor_get(v_dt_2593_, 1);
                    lean_dec(v_unused_2619_);
                    v___x_2597_ = v_dt_2593_;
                    v_isShared_2598_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2595_);
                    lean_dec(v_dt_2593_);
                    v___x_2597_ = lean_box(0);
                    v_isShared_2598_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2599_ = lean_ctor_get(v_timestamp_2595_, 0);
                lean_inc(v_second_2599_);
                v_nano_2600_ = lean_ctor_get(v_timestamp_2595_, 1);
                lean_inc(v_nano_2600_);
                lean_dec_ref(v_timestamp_2595_);
                v___x_2601_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_addMilliseconds___closed__0,
                );
                v___x_2602_ = lean_int_mul(v_milliseconds_2594_, v___x_2601_);
                v___x_2603_ = l_Std_Time_Duration_ofNanoseconds(v___x_2602_);
                lean_dec(v___x_2602_);
                v_second_2604_ = lean_ctor_get(v___x_2603_, 0);
                lean_inc(v_second_2604_);
                v_nano_2605_ = lean_ctor_get(v___x_2603_, 1);
                lean_inc(v_nano_2605_);
                lean_dec_ref(v___x_2603_);
                v___x_2606_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2607_ = lean_int_mul(v_second_2599_, v___x_2606_);
                lean_dec(v_second_2599_);
                v___x_2608_ = lean_int_add(v___x_2607_, v_nano_2600_);
                lean_dec(v_nano_2600_);
                lean_dec(v___x_2607_);
                v___x_2609_ = lean_int_mul(v_second_2604_, v___x_2606_);
                lean_dec(v_second_2604_);
                v___x_2610_ = lean_int_add(v___x_2609_, v_nano_2605_);
                lean_dec(v_nano_2605_);
                lean_dec(v___x_2609_);
                v___x_2611_ = lean_int_add(v___x_2608_, v___x_2610_);
                lean_dec(v___x_2610_);
                lean_dec(v___x_2608_);
                v___x_2612_ = l_Std_Time_Duration_ofNanoseconds(v___x_2611_);
                lean_dec(v___x_2611_);
                lean_inc_ref(v___x_2612_);
                v___f_2613_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2613_, 0, v_tz_2592_);
                lean_closure_set(v___f_2613_, 1, v___x_2612_);
                lean_closure_set(v___f_2613_, 2, v___x_2606_);
                v___x_2614_ = lean_mk_thunk(v___f_2613_);
                if v_isShared_2598_ == 0 {
                    lean_ctor_set(v___x_2597_, 1, v___x_2614_);
                    lean_ctor_set(v___x_2597_, 0, v___x_2612_);
                    v___x_2616_ = v___x_2597_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2612_);
                    lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2614_);
                    v___x_2616_ = v_reuseFailAlloc_2617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addMilliseconds___boxed(
    mut v_tz_2620_: *mut LeanObject,
    mut v_dt_2621_: *mut LeanObject,
    mut v_milliseconds_2622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2623_: *mut LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_Std_Time_DateTime_addMilliseconds(v_tz_2620_, v_dt_2621_, v_milliseconds_2622_);
    lean_dec(v_milliseconds_2622_);
    return v_res_2623_;
}
pub unsafe fn l_Std_Time_DateTime_subMilliseconds(
    mut v_tz_2624_: *mut LeanObject,
    mut v_dt_2625_: *mut LeanObject,
    mut v_milliseconds_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_unused_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2627_ = lean_ctor_get(v_dt_2625_, 0);
                v_isSharedCheck_2652_ = (!lean_is_exclusive(v_dt_2625_)) as u8;
                if v_isSharedCheck_2652_ == 0 {
                    v_unused_2653_ = lean_ctor_get(v_dt_2625_, 1);
                    lean_dec(v_unused_2653_);
                    v___x_2629_ = v_dt_2625_;
                    v_isShared_2630_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2627_);
                    lean_dec(v_dt_2625_);
                    v___x_2629_ = lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2631_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_addMilliseconds___closed__0,
                );
                v___x_2632_ = lean_int_mul(v_milliseconds_2626_, v___x_2631_);
                v___x_2633_ = l_Std_Time_Duration_ofNanoseconds(v___x_2632_);
                lean_dec(v___x_2632_);
                v_second_2634_ = lean_ctor_get(v___x_2633_, 0);
                lean_inc(v_second_2634_);
                v_nano_2635_ = lean_ctor_get(v___x_2633_, 1);
                lean_inc(v_nano_2635_);
                lean_dec_ref(v___x_2633_);
                v_second_2636_ = lean_ctor_get(v_timestamp_2627_, 0);
                lean_inc(v_second_2636_);
                v_nano_2637_ = lean_ctor_get(v_timestamp_2627_, 1);
                lean_inc(v_nano_2637_);
                lean_dec_ref(v_timestamp_2627_);
                v___x_2638_ = lean_int_neg(v_second_2634_);
                lean_dec(v_second_2634_);
                v___x_2639_ = lean_int_neg(v_nano_2635_);
                lean_dec(v_nano_2635_);
                v___x_2640_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2641_ = lean_int_mul(v_second_2636_, v___x_2640_);
                lean_dec(v_second_2636_);
                v___x_2642_ = lean_int_add(v___x_2641_, v_nano_2637_);
                lean_dec(v_nano_2637_);
                lean_dec(v___x_2641_);
                v___x_2643_ = lean_int_mul(v___x_2638_, v___x_2640_);
                lean_dec(v___x_2638_);
                v___x_2644_ = lean_int_add(v___x_2643_, v___x_2639_);
                lean_dec(v___x_2639_);
                lean_dec(v___x_2643_);
                v___x_2645_ = lean_int_add(v___x_2642_, v___x_2644_);
                lean_dec(v___x_2644_);
                lean_dec(v___x_2642_);
                v___x_2646_ = l_Std_Time_Duration_ofNanoseconds(v___x_2645_);
                lean_dec(v___x_2645_);
                lean_inc_ref(v___x_2646_);
                v___f_2647_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2647_, 0, v_tz_2624_);
                lean_closure_set(v___f_2647_, 1, v___x_2646_);
                lean_closure_set(v___f_2647_, 2, v___x_2640_);
                v___x_2648_ = lean_mk_thunk(v___f_2647_);
                if v_isShared_2630_ == 0 {
                    lean_ctor_set(v___x_2629_, 1, v___x_2648_);
                    lean_ctor_set(v___x_2629_, 0, v___x_2646_);
                    v___x_2650_ = v___x_2629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2646_);
                    lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2648_);
                    v___x_2650_ = v_reuseFailAlloc_2651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subMilliseconds___boxed(
    mut v_tz_2654_: *mut LeanObject,
    mut v_dt_2655_: *mut LeanObject,
    mut v_milliseconds_2656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2657_: *mut LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Std_Time_DateTime_subMilliseconds(v_tz_2654_, v_dt_2655_, v_milliseconds_2656_);
    lean_dec(v_milliseconds_2656_);
    return v_res_2657_;
}
pub unsafe fn l_Std_Time_DateTime_addNanoseconds(
    mut v_tz_2658_: *mut LeanObject,
    mut v_dt_2659_: *mut LeanObject,
    mut v_nanoseconds_2660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v_second_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2682_: u8 = 0;
    let mut v_unused_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2661_ = lean_ctor_get(v_dt_2659_, 0);
                v_isSharedCheck_2682_ = (!lean_is_exclusive(v_dt_2659_)) as u8;
                if v_isSharedCheck_2682_ == 0 {
                    v_unused_2683_ = lean_ctor_get(v_dt_2659_, 1);
                    lean_dec(v_unused_2683_);
                    v___x_2663_ = v_dt_2659_;
                    v_isShared_2664_ = v_isSharedCheck_2682_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2661_);
                    lean_dec(v_dt_2659_);
                    v___x_2663_ = lean_box(0);
                    v_isShared_2664_ = v_isSharedCheck_2682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2665_ = lean_ctor_get(v_timestamp_2661_, 0);
                lean_inc(v_second_2665_);
                v_nano_2666_ = lean_ctor_get(v_timestamp_2661_, 1);
                lean_inc(v_nano_2666_);
                lean_dec_ref(v_timestamp_2661_);
                v___x_2667_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_2660_);
                v_second_2668_ = lean_ctor_get(v___x_2667_, 0);
                lean_inc(v_second_2668_);
                v_nano_2669_ = lean_ctor_get(v___x_2667_, 1);
                lean_inc(v_nano_2669_);
                lean_dec_ref(v___x_2667_);
                v___x_2670_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2671_ = lean_int_mul(v_second_2665_, v___x_2670_);
                lean_dec(v_second_2665_);
                v___x_2672_ = lean_int_add(v___x_2671_, v_nano_2666_);
                lean_dec(v_nano_2666_);
                lean_dec(v___x_2671_);
                v___x_2673_ = lean_int_mul(v_second_2668_, v___x_2670_);
                lean_dec(v_second_2668_);
                v___x_2674_ = lean_int_add(v___x_2673_, v_nano_2669_);
                lean_dec(v_nano_2669_);
                lean_dec(v___x_2673_);
                v___x_2675_ = lean_int_add(v___x_2672_, v___x_2674_);
                lean_dec(v___x_2674_);
                lean_dec(v___x_2672_);
                v___x_2676_ = l_Std_Time_Duration_ofNanoseconds(v___x_2675_);
                lean_dec(v___x_2675_);
                lean_inc_ref(v___x_2676_);
                v___f_2677_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2677_, 0, v_tz_2658_);
                lean_closure_set(v___f_2677_, 1, v___x_2676_);
                lean_closure_set(v___f_2677_, 2, v___x_2670_);
                v___x_2678_ = lean_mk_thunk(v___f_2677_);
                if v_isShared_2664_ == 0 {
                    lean_ctor_set(v___x_2663_, 1, v___x_2678_);
                    lean_ctor_set(v___x_2663_, 0, v___x_2676_);
                    v___x_2680_ = v___x_2663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2676_);
                    lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2678_);
                    v___x_2680_ = v_reuseFailAlloc_2681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addNanoseconds___boxed(
    mut v_tz_2684_: *mut LeanObject,
    mut v_dt_2685_: *mut LeanObject,
    mut v_nanoseconds_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2687_: *mut LeanObject = core::ptr::null_mut();
    v_res_2687_ = l_Std_Time_DateTime_addNanoseconds(v_tz_2684_, v_dt_2685_, v_nanoseconds_2686_);
    lean_dec(v_nanoseconds_2686_);
    return v_res_2687_;
}
pub unsafe fn l_Std_Time_DateTime_subNanoseconds(
    mut v_tz_2688_: *mut LeanObject,
    mut v_dt_2689_: *mut LeanObject,
    mut v_nanoseconds_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_unused_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2691_ = lean_ctor_get(v_dt_2689_, 0);
                v_isSharedCheck_2714_ = (!lean_is_exclusive(v_dt_2689_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v_unused_2715_ = lean_ctor_get(v_dt_2689_, 1);
                    lean_dec(v_unused_2715_);
                    v___x_2693_ = v_dt_2689_;
                    v_isShared_2694_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2691_);
                    lean_dec(v_dt_2689_);
                    v___x_2693_ = lean_box(0);
                    v_isShared_2694_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2695_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_2690_);
                v_second_2696_ = lean_ctor_get(v___x_2695_, 0);
                lean_inc(v_second_2696_);
                v_nano_2697_ = lean_ctor_get(v___x_2695_, 1);
                lean_inc(v_nano_2697_);
                lean_dec_ref(v___x_2695_);
                v_second_2698_ = lean_ctor_get(v_timestamp_2691_, 0);
                lean_inc(v_second_2698_);
                v_nano_2699_ = lean_ctor_get(v_timestamp_2691_, 1);
                lean_inc(v_nano_2699_);
                lean_dec_ref(v_timestamp_2691_);
                v___x_2700_ = lean_int_neg(v_second_2696_);
                lean_dec(v_second_2696_);
                v___x_2701_ = lean_int_neg(v_nano_2697_);
                lean_dec(v_nano_2697_);
                v___x_2702_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2703_ = lean_int_mul(v_second_2698_, v___x_2702_);
                lean_dec(v_second_2698_);
                v___x_2704_ = lean_int_add(v___x_2703_, v_nano_2699_);
                lean_dec(v_nano_2699_);
                lean_dec(v___x_2703_);
                v___x_2705_ = lean_int_mul(v___x_2700_, v___x_2702_);
                lean_dec(v___x_2700_);
                v___x_2706_ = lean_int_add(v___x_2705_, v___x_2701_);
                lean_dec(v___x_2701_);
                lean_dec(v___x_2705_);
                v___x_2707_ = lean_int_add(v___x_2704_, v___x_2706_);
                lean_dec(v___x_2706_);
                lean_dec(v___x_2704_);
                v___x_2708_ = l_Std_Time_Duration_ofNanoseconds(v___x_2707_);
                lean_dec(v___x_2707_);
                lean_inc_ref(v___x_2708_);
                v___f_2709_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_2709_, 0, v_tz_2688_);
                lean_closure_set(v___f_2709_, 1, v___x_2708_);
                lean_closure_set(v___f_2709_, 2, v___x_2702_);
                v___x_2710_ = lean_mk_thunk(v___f_2709_);
                if v_isShared_2694_ == 0 {
                    lean_ctor_set(v___x_2693_, 1, v___x_2710_);
                    lean_ctor_set(v___x_2693_, 0, v___x_2708_);
                    v___x_2712_ = v___x_2693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2708_);
                    lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2710_);
                    v___x_2712_ = v_reuseFailAlloc_2713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subNanoseconds___boxed(
    mut v_tz_2716_: *mut LeanObject,
    mut v_dt_2717_: *mut LeanObject,
    mut v_nanoseconds_2718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2719_: *mut LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Std_Time_DateTime_subNanoseconds(v_tz_2716_, v_dt_2717_, v_nanoseconds_2718_);
    lean_dec(v_nanoseconds_2718_);
    return v_res_2719_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addDays___closed__0() -> *mut LeanObject {
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    v___x_2720_ = lean_unsigned_to_nat(86400);
    v___x_2721_ = lean_nat_to_int(v___x_2720_);
    return v___x_2721_;
}
pub unsafe fn l_Std_Time_DateTime_addDays(
    mut v_tz_2722_: *mut LeanObject,
    mut v_dt_2723_: *mut LeanObject,
    mut v_days_2724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v_second_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_unused_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2725_ = lean_ctor_get(v_dt_2723_, 0);
                v_isSharedCheck_2746_ = (!lean_is_exclusive(v_dt_2723_)) as u8;
                if v_isSharedCheck_2746_ == 0 {
                    v_unused_2747_ = lean_ctor_get(v_dt_2723_, 1);
                    lean_dec(v_unused_2747_);
                    v___x_2727_ = v_dt_2723_;
                    v_isShared_2728_ = v_isSharedCheck_2746_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2725_);
                    lean_dec(v_dt_2723_);
                    v___x_2727_ = lean_box(0);
                    v_isShared_2728_ = v_isSharedCheck_2746_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2729_ = lean_ctor_get(v_timestamp_2725_, 0);
                lean_inc(v_second_2729_);
                v_nano_2730_ = lean_ctor_get(v_timestamp_2725_, 1);
                lean_inc(v_nano_2730_);
                lean_dec_ref(v_timestamp_2725_);
                v___x_2731_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2732_ = lean_int_mul(v_days_2724_, v___x_2731_);
                v___x_2733_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2734_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2735_ = lean_int_mul(v_second_2729_, v___x_2734_);
                lean_dec(v_second_2729_);
                v___x_2736_ = lean_int_add(v___x_2735_, v_nano_2730_);
                lean_dec(v_nano_2730_);
                lean_dec(v___x_2735_);
                v___x_2737_ = lean_int_mul(v___x_2732_, v___x_2734_);
                lean_dec(v___x_2732_);
                v___x_2738_ = lean_int_add(v___x_2737_, v___x_2733_);
                lean_dec(v___x_2737_);
                v___x_2739_ = lean_int_add(v___x_2736_, v___x_2738_);
                lean_dec(v___x_2738_);
                lean_dec(v___x_2736_);
                v___x_2740_ = l_Std_Time_Duration_ofNanoseconds(v___x_2739_);
                lean_dec(v___x_2739_);
                lean_inc_ref(v___x_2740_);
                v___f_2741_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2741_, 0, v_tz_2722_);
                lean_closure_set(v___f_2741_, 1, v___x_2740_);
                lean_closure_set(v___f_2741_, 2, v___x_2734_);
                lean_closure_set(v___f_2741_, 3, v___x_2733_);
                v___x_2742_ = lean_mk_thunk(v___f_2741_);
                if v_isShared_2728_ == 0 {
                    lean_ctor_set(v___x_2727_, 1, v___x_2742_);
                    lean_ctor_set(v___x_2727_, 0, v___x_2740_);
                    v___x_2744_ = v___x_2727_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2740_);
                    lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2742_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addDays___boxed(
    mut v_tz_2748_: *mut LeanObject,
    mut v_dt_2749_: *mut LeanObject,
    mut v_days_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2751_: *mut LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Std_Time_DateTime_addDays(v_tz_2748_, v_dt_2749_, v_days_2750_);
    lean_dec(v_days_2750_);
    return v_res_2751_;
}
pub unsafe fn l_Std_Time_DateTime_subDays(
    mut v_tz_2752_: *mut LeanObject,
    mut v_dt_2753_: *mut LeanObject,
    mut v_days_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v_second_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2778_: u8 = 0;
    let mut v_unused_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2755_ = lean_ctor_get(v_dt_2753_, 0);
                v_isSharedCheck_2778_ = (!lean_is_exclusive(v_dt_2753_)) as u8;
                if v_isSharedCheck_2778_ == 0 {
                    v_unused_2779_ = lean_ctor_get(v_dt_2753_, 1);
                    lean_dec(v_unused_2779_);
                    v___x_2757_ = v_dt_2753_;
                    v_isShared_2758_ = v_isSharedCheck_2778_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2755_);
                    lean_dec(v_dt_2753_);
                    v___x_2757_ = lean_box(0);
                    v_isShared_2758_ = v_isSharedCheck_2778_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2759_ = lean_ctor_get(v_timestamp_2755_, 0);
                lean_inc(v_second_2759_);
                v_nano_2760_ = lean_ctor_get(v_timestamp_2755_, 1);
                lean_inc(v_nano_2760_);
                lean_dec_ref(v_timestamp_2755_);
                v___x_2761_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2762_ = lean_int_mul(v_days_2754_, v___x_2761_);
                v___x_2763_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2764_ = lean_int_neg(v___x_2762_);
                lean_dec(v___x_2762_);
                v___x_2765_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2766_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2767_ = lean_int_mul(v_second_2759_, v___x_2766_);
                lean_dec(v_second_2759_);
                v___x_2768_ = lean_int_add(v___x_2767_, v_nano_2760_);
                lean_dec(v_nano_2760_);
                lean_dec(v___x_2767_);
                v___x_2769_ = lean_int_mul(v___x_2764_, v___x_2766_);
                lean_dec(v___x_2764_);
                v___x_2770_ = lean_int_add(v___x_2769_, v___x_2765_);
                lean_dec(v___x_2769_);
                v___x_2771_ = lean_int_add(v___x_2768_, v___x_2770_);
                lean_dec(v___x_2770_);
                lean_dec(v___x_2768_);
                v___x_2772_ = l_Std_Time_Duration_ofNanoseconds(v___x_2771_);
                lean_dec(v___x_2771_);
                lean_inc_ref(v___x_2772_);
                v___f_2773_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2773_, 0, v_tz_2752_);
                lean_closure_set(v___f_2773_, 1, v___x_2772_);
                lean_closure_set(v___f_2773_, 2, v___x_2766_);
                lean_closure_set(v___f_2773_, 3, v___x_2763_);
                v___x_2774_ = lean_mk_thunk(v___f_2773_);
                if v_isShared_2758_ == 0 {
                    lean_ctor_set(v___x_2757_, 1, v___x_2774_);
                    lean_ctor_set(v___x_2757_, 0, v___x_2772_);
                    v___x_2776_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2772_);
                    lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
                    v___x_2776_ = v_reuseFailAlloc_2777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subDays___boxed(
    mut v_tz_2780_: *mut LeanObject,
    mut v_dt_2781_: *mut LeanObject,
    mut v_days_2782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2783_: *mut LeanObject = core::ptr::null_mut();
    v_res_2783_ = l_Std_Time_DateTime_subDays(v_tz_2780_, v_dt_2781_, v_days_2782_);
    lean_dec(v_days_2782_);
    return v_res_2783_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addWeeks___closed__0() -> *mut LeanObject {
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    v___x_2784_ = lean_unsigned_to_nat(7);
    v___x_2785_ = lean_nat_to_int(v___x_2784_);
    return v___x_2785_;
}
pub unsafe fn l_Std_Time_DateTime_addWeeks(
    mut v_tz_2786_: *mut LeanObject,
    mut v_dt_2787_: *mut LeanObject,
    mut v_weeks_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v_second_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2812_: u8 = 0;
    let mut v_unused_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2789_ = lean_ctor_get(v_dt_2787_, 0);
                v_isSharedCheck_2812_ = (!lean_is_exclusive(v_dt_2787_)) as u8;
                if v_isSharedCheck_2812_ == 0 {
                    v_unused_2813_ = lean_ctor_get(v_dt_2787_, 1);
                    lean_dec(v_unused_2813_);
                    v___x_2791_ = v_dt_2787_;
                    v_isShared_2792_ = v_isSharedCheck_2812_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2789_);
                    lean_dec(v_dt_2787_);
                    v___x_2791_ = lean_box(0);
                    v_isShared_2792_ = v_isSharedCheck_2812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2793_ = lean_ctor_get(v_timestamp_2789_, 0);
                lean_inc(v_second_2793_);
                v_nano_2794_ = lean_ctor_get(v_timestamp_2789_, 1);
                lean_inc(v_nano_2794_);
                lean_dec_ref(v_timestamp_2789_);
                v___x_2795_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_DateTime_addWeeks___closed__0,
                );
                v___x_2796_ = lean_int_mul(v_weeks_2788_, v___x_2795_);
                v___x_2797_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2798_ = lean_int_mul(v___x_2796_, v___x_2797_);
                lean_dec(v___x_2796_);
                v___x_2799_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2800_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2801_ = lean_int_mul(v_second_2793_, v___x_2800_);
                lean_dec(v_second_2793_);
                v___x_2802_ = lean_int_add(v___x_2801_, v_nano_2794_);
                lean_dec(v_nano_2794_);
                lean_dec(v___x_2801_);
                v___x_2803_ = lean_int_mul(v___x_2798_, v___x_2800_);
                lean_dec(v___x_2798_);
                v___x_2804_ = lean_int_add(v___x_2803_, v___x_2799_);
                lean_dec(v___x_2803_);
                v___x_2805_ = lean_int_add(v___x_2802_, v___x_2804_);
                lean_dec(v___x_2804_);
                lean_dec(v___x_2802_);
                v___x_2806_ = l_Std_Time_Duration_ofNanoseconds(v___x_2805_);
                lean_dec(v___x_2805_);
                lean_inc_ref(v___x_2806_);
                v___f_2807_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2807_, 0, v_tz_2786_);
                lean_closure_set(v___f_2807_, 1, v___x_2806_);
                lean_closure_set(v___f_2807_, 2, v___x_2800_);
                lean_closure_set(v___f_2807_, 3, v___x_2799_);
                v___x_2808_ = lean_mk_thunk(v___f_2807_);
                if v_isShared_2792_ == 0 {
                    lean_ctor_set(v___x_2791_, 1, v___x_2808_);
                    lean_ctor_set(v___x_2791_, 0, v___x_2806_);
                    v___x_2810_ = v___x_2791_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2806_);
                    lean_ctor_set(v_reuseFailAlloc_2811_, 1, v___x_2808_);
                    v___x_2810_ = v_reuseFailAlloc_2811_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addWeeks___boxed(
    mut v_tz_2814_: *mut LeanObject,
    mut v_dt_2815_: *mut LeanObject,
    mut v_weeks_2816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2817_: *mut LeanObject = core::ptr::null_mut();
    v_res_2817_ = l_Std_Time_DateTime_addWeeks(v_tz_2814_, v_dt_2815_, v_weeks_2816_);
    lean_dec(v_weeks_2816_);
    return v_res_2817_;
}
pub unsafe fn l_Std_Time_DateTime_subWeeks(
    mut v_tz_2818_: *mut LeanObject,
    mut v_dt_2819_: *mut LeanObject,
    mut v_weeks_2820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v_second_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v_unused_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2821_ = lean_ctor_get(v_dt_2819_, 0);
                v_isSharedCheck_2846_ = (!lean_is_exclusive(v_dt_2819_)) as u8;
                if v_isSharedCheck_2846_ == 0 {
                    v_unused_2847_ = lean_ctor_get(v_dt_2819_, 1);
                    lean_dec(v_unused_2847_);
                    v___x_2823_ = v_dt_2819_;
                    v_isShared_2824_ = v_isSharedCheck_2846_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_2821_);
                    lean_dec(v_dt_2819_);
                    v___x_2823_ = lean_box(0);
                    v_isShared_2824_ = v_isSharedCheck_2846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2825_ = lean_ctor_get(v_timestamp_2821_, 0);
                lean_inc(v_second_2825_);
                v_nano_2826_ = lean_ctor_get(v_timestamp_2821_, 1);
                lean_inc(v_nano_2826_);
                lean_dec_ref(v_timestamp_2821_);
                v___x_2827_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_DateTime_addWeeks___closed__0,
                );
                v___x_2828_ = lean_int_mul(v_weeks_2820_, v___x_2827_);
                v___x_2829_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2830_ = lean_int_mul(v___x_2828_, v___x_2829_);
                lean_dec(v___x_2828_);
                v___x_2831_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2832_ = lean_int_neg(v___x_2830_);
                lean_dec(v___x_2830_);
                v___x_2833_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2834_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2835_ = lean_int_mul(v_second_2825_, v___x_2834_);
                lean_dec(v_second_2825_);
                v___x_2836_ = lean_int_add(v___x_2835_, v_nano_2826_);
                lean_dec(v_nano_2826_);
                lean_dec(v___x_2835_);
                v___x_2837_ = lean_int_mul(v___x_2832_, v___x_2834_);
                lean_dec(v___x_2832_);
                v___x_2838_ = lean_int_add(v___x_2837_, v___x_2833_);
                lean_dec(v___x_2837_);
                v___x_2839_ = lean_int_add(v___x_2836_, v___x_2838_);
                lean_dec(v___x_2838_);
                lean_dec(v___x_2836_);
                v___x_2840_ = l_Std_Time_Duration_ofNanoseconds(v___x_2839_);
                lean_dec(v___x_2839_);
                lean_inc_ref(v___x_2840_);
                v___f_2841_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                lean_closure_set(v___f_2841_, 0, v_tz_2818_);
                lean_closure_set(v___f_2841_, 1, v___x_2840_);
                lean_closure_set(v___f_2841_, 2, v___x_2834_);
                lean_closure_set(v___f_2841_, 3, v___x_2831_);
                v___x_2842_ = lean_mk_thunk(v___f_2841_);
                if v_isShared_2824_ == 0 {
                    lean_ctor_set(v___x_2823_, 1, v___x_2842_);
                    lean_ctor_set(v___x_2823_, 0, v___x_2840_);
                    v___x_2844_ = v___x_2823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2840_);
                    lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2842_);
                    v___x_2844_ = v_reuseFailAlloc_2845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subWeeks___boxed(
    mut v_tz_2848_: *mut LeanObject,
    mut v_dt_2849_: *mut LeanObject,
    mut v_weeks_2850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2851_: *mut LeanObject = core::ptr::null_mut();
    v_res_2851_ = l_Std_Time_DateTime_subWeeks(v_tz_2848_, v_dt_2849_, v_weeks_2850_);
    lean_dec(v_weeks_2850_);
    return v_res_2851_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsClip___lam__0(
    mut v___x_2852_: *mut LeanObject,
    mut v_x_2853_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___x_2852_);
    return v___x_2852_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(
    mut v___x_2854_: *mut LeanObject,
    mut v_x_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2856_: *mut LeanObject = core::ptr::null_mut();
    v_res_2856_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_2854_, v_x_2855_);
    lean_dec_ref(v___x_2854_);
    return v_res_2856_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsClip(
    mut v_tz_2857_: *mut LeanObject,
    mut v_dt_2858_: *mut LeanObject,
    mut v_months_2859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v_offset_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut v_unused_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2860_ = lean_ctor_get(v_dt_2858_, 1);
                v_isSharedCheck_2884_ = (!lean_is_exclusive(v_dt_2858_)) as u8;
                if v_isSharedCheck_2884_ == 0 {
                    v_unused_2885_ = lean_ctor_get(v_dt_2858_, 0);
                    lean_dec(v_unused_2885_);
                    v___x_2862_ = v_dt_2858_;
                    v_isShared_2863_ = v_isSharedCheck_2884_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_2860_);
                    lean_dec(v_dt_2858_);
                    v___x_2862_ = lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_offset_2864_ = lean_ctor_get(v_tz_2857_, 0);
                v___x_2865_ = lean_thunk_get_own(v_date_2860_);
                lean_dec_ref(v_date_2860_);
                v___x_2866_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_2865_, v_months_2859_);
                lean_inc_ref(v___x_2866_);
                v___x_2867_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2866_);
                v_second_2868_ = lean_ctor_get(v___x_2867_, 0);
                lean_inc(v_second_2868_);
                v_nano_2869_ = lean_ctor_get(v___x_2867_, 1);
                lean_inc(v_nano_2869_);
                lean_dec_ref(v___x_2867_);
                v___f_2870_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2870_, 0, v___x_2866_);
                v___x_2871_ = lean_int_neg(v_offset_2864_);
                v___x_2872_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2873_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2874_ = lean_int_mul(v_second_2868_, v___x_2873_);
                lean_dec(v_second_2868_);
                v___x_2875_ = lean_int_add(v___x_2874_, v_nano_2869_);
                lean_dec(v_nano_2869_);
                lean_dec(v___x_2874_);
                v___x_2876_ = lean_int_mul(v___x_2871_, v___x_2873_);
                lean_dec(v___x_2871_);
                v___x_2877_ = lean_int_add(v___x_2876_, v___x_2872_);
                lean_dec(v___x_2876_);
                v___x_2878_ = lean_int_add(v___x_2875_, v___x_2877_);
                lean_dec(v___x_2877_);
                lean_dec(v___x_2875_);
                v_tm_2879_ = l_Std_Time_Duration_ofNanoseconds(v___x_2878_);
                lean_dec(v___x_2878_);
                v___x_2880_ = lean_mk_thunk(v___f_2870_);
                if v_isShared_2863_ == 0 {
                    lean_ctor_set(v___x_2862_, 1, v___x_2880_);
                    lean_ctor_set(v___x_2862_, 0, v_tm_2879_);
                    v___x_2882_ = v___x_2862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_tm_2879_);
                    lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2880_);
                    v___x_2882_ = v_reuseFailAlloc_2883_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addMonthsClip___boxed(
    mut v_tz_2886_: *mut LeanObject,
    mut v_dt_2887_: *mut LeanObject,
    mut v_months_2888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2889_: *mut LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Std_Time_DateTime_addMonthsClip(v_tz_2886_, v_dt_2887_, v_months_2888_);
    lean_dec(v_months_2888_);
    lean_dec_ref(v_tz_2886_);
    return v_res_2889_;
}
pub unsafe fn l_Std_Time_DateTime_subMonthsClip(
    mut v_tz_2890_: *mut LeanObject,
    mut v_dt_2891_: *mut LeanObject,
    mut v_months_2892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v_offset_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_isSharedCheck_2927_: u8 = 0;
    let mut v_unused_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2893_ = lean_ctor_get(v_dt_2891_, 1);
                v_isSharedCheck_2927_ = (!lean_is_exclusive(v_dt_2891_)) as u8;
                if v_isSharedCheck_2927_ == 0 {
                    v_unused_2928_ = lean_ctor_get(v_dt_2891_, 0);
                    lean_dec(v_unused_2928_);
                    v___x_2895_ = v_dt_2891_;
                    v_isShared_2896_ = v_isSharedCheck_2927_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_2893_);
                    lean_dec(v_dt_2891_);
                    v___x_2895_ = lean_box(0);
                    v_isShared_2896_ = v_isSharedCheck_2927_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2897_ = lean_thunk_get_own(v_date_2893_);
                lean_dec_ref(v_date_2893_);
                v_date_2898_ = lean_ctor_get(v___x_2897_, 0);
                v_time_2899_ = lean_ctor_get(v___x_2897_, 1);
                v_isSharedCheck_2926_ = (!lean_is_exclusive(v___x_2897_)) as u8;
                if v_isSharedCheck_2926_ == 0 {
                    v___x_2901_ = v___x_2897_;
                    v_isShared_2902_ = v_isSharedCheck_2926_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_2899_);
                    lean_inc(v_date_2898_);
                    lean_dec(v___x_2897_);
                    v___x_2901_ = lean_box(0);
                    v_isShared_2902_ = v_isSharedCheck_2926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_2903_ = lean_ctor_get(v_tz_2890_, 0);
                v___x_2904_ = lean_int_neg(v_months_2892_);
                v___x_2905_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2898_, v___x_2904_);
                lean_dec(v___x_2904_);
                if v_isShared_2902_ == 0 {
                    lean_ctor_set(v___x_2901_, 0, v___x_2905_);
                    v___x_2907_ = v___x_2901_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2905_);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_time_2899_);
                    v___x_2907_ = v_reuseFailAlloc_2925_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2907_);
                v___x_2908_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2907_);
                v_second_2909_ = lean_ctor_get(v___x_2908_, 0);
                lean_inc(v_second_2909_);
                v_nano_2910_ = lean_ctor_get(v___x_2908_, 1);
                lean_inc(v_nano_2910_);
                lean_dec_ref(v___x_2908_);
                v___f_2911_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2911_, 0, v___x_2907_);
                v___x_2912_ = lean_int_neg(v_offset_2903_);
                v___x_2913_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2914_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2915_ = lean_int_mul(v_second_2909_, v___x_2914_);
                lean_dec(v_second_2909_);
                v___x_2916_ = lean_int_add(v___x_2915_, v_nano_2910_);
                lean_dec(v_nano_2910_);
                lean_dec(v___x_2915_);
                v___x_2917_ = lean_int_mul(v___x_2912_, v___x_2914_);
                lean_dec(v___x_2912_);
                v___x_2918_ = lean_int_add(v___x_2917_, v___x_2913_);
                lean_dec(v___x_2917_);
                v___x_2919_ = lean_int_add(v___x_2916_, v___x_2918_);
                lean_dec(v___x_2918_);
                lean_dec(v___x_2916_);
                v_tm_2920_ = l_Std_Time_Duration_ofNanoseconds(v___x_2919_);
                lean_dec(v___x_2919_);
                v___x_2921_ = lean_mk_thunk(v___f_2911_);
                if v_isShared_2896_ == 0 {
                    lean_ctor_set(v___x_2895_, 1, v___x_2921_);
                    lean_ctor_set(v___x_2895_, 0, v_tm_2920_);
                    v___x_2923_ = v___x_2895_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_tm_2920_);
                    lean_ctor_set(v_reuseFailAlloc_2924_, 1, v___x_2921_);
                    v___x_2923_ = v_reuseFailAlloc_2924_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subMonthsClip___boxed(
    mut v_tz_2929_: *mut LeanObject,
    mut v_dt_2930_: *mut LeanObject,
    mut v_months_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2932_: *mut LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Std_Time_DateTime_subMonthsClip(v_tz_2929_, v_dt_2930_, v_months_2931_);
    lean_dec(v_months_2931_);
    lean_dec_ref(v_tz_2929_);
    return v_res_2932_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsRollOver(
    mut v_tz_2933_: *mut LeanObject,
    mut v_dt_2934_: *mut LeanObject,
    mut v_months_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_offset_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_unused_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2936_ = lean_ctor_get(v_dt_2934_, 1);
                v_isSharedCheck_2960_ = (!lean_is_exclusive(v_dt_2934_)) as u8;
                if v_isSharedCheck_2960_ == 0 {
                    v_unused_2961_ = lean_ctor_get(v_dt_2934_, 0);
                    lean_dec(v_unused_2961_);
                    v___x_2938_ = v_dt_2934_;
                    v_isShared_2939_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_2936_);
                    lean_dec(v_dt_2934_);
                    v___x_2938_ = lean_box(0);
                    v_isShared_2939_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_offset_2940_ = lean_ctor_get(v_tz_2933_, 0);
                v___x_2941_ = lean_thunk_get_own(v_date_2936_);
                lean_dec_ref(v_date_2936_);
                v___x_2942_ =
                    l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_2941_, v_months_2935_);
                lean_inc_ref(v___x_2942_);
                v___x_2943_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2942_);
                v_second_2944_ = lean_ctor_get(v___x_2943_, 0);
                lean_inc(v_second_2944_);
                v_nano_2945_ = lean_ctor_get(v___x_2943_, 1);
                lean_inc(v_nano_2945_);
                lean_dec_ref(v___x_2943_);
                v___f_2946_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2946_, 0, v___x_2942_);
                v___x_2947_ = lean_int_neg(v_offset_2940_);
                v___x_2948_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2949_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2950_ = lean_int_mul(v_second_2944_, v___x_2949_);
                lean_dec(v_second_2944_);
                v___x_2951_ = lean_int_add(v___x_2950_, v_nano_2945_);
                lean_dec(v_nano_2945_);
                lean_dec(v___x_2950_);
                v___x_2952_ = lean_int_mul(v___x_2947_, v___x_2949_);
                lean_dec(v___x_2947_);
                v___x_2953_ = lean_int_add(v___x_2952_, v___x_2948_);
                lean_dec(v___x_2952_);
                v___x_2954_ = lean_int_add(v___x_2951_, v___x_2953_);
                lean_dec(v___x_2953_);
                lean_dec(v___x_2951_);
                v_tm_2955_ = l_Std_Time_Duration_ofNanoseconds(v___x_2954_);
                lean_dec(v___x_2954_);
                v___x_2956_ = lean_mk_thunk(v___f_2946_);
                if v_isShared_2939_ == 0 {
                    lean_ctor_set(v___x_2938_, 1, v___x_2956_);
                    lean_ctor_set(v___x_2938_, 0, v_tm_2955_);
                    v___x_2958_ = v___x_2938_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_tm_2955_);
                    lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2956_);
                    v___x_2958_ = v_reuseFailAlloc_2959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addMonthsRollOver___boxed(
    mut v_tz_2962_: *mut LeanObject,
    mut v_dt_2963_: *mut LeanObject,
    mut v_months_2964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2965_: *mut LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Std_Time_DateTime_addMonthsRollOver(v_tz_2962_, v_dt_2963_, v_months_2964_);
    lean_dec(v_months_2964_);
    lean_dec_ref(v_tz_2962_);
    return v_res_2965_;
}
pub unsafe fn l_Std_Time_DateTime_subMonthsRollOver(
    mut v_tz_2966_: *mut LeanObject,
    mut v_dt_2967_: *mut LeanObject,
    mut v_months_2968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v_offset_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v_unused_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2969_ = lean_ctor_get(v_dt_2967_, 1);
                v_isSharedCheck_3003_ = (!lean_is_exclusive(v_dt_2967_)) as u8;
                if v_isSharedCheck_3003_ == 0 {
                    v_unused_3004_ = lean_ctor_get(v_dt_2967_, 0);
                    lean_dec(v_unused_3004_);
                    v___x_2971_ = v_dt_2967_;
                    v_isShared_2972_ = v_isSharedCheck_3003_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_2969_);
                    lean_dec(v_dt_2967_);
                    v___x_2971_ = lean_box(0);
                    v_isShared_2972_ = v_isSharedCheck_3003_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2973_ = lean_thunk_get_own(v_date_2969_);
                lean_dec_ref(v_date_2969_);
                v_date_2974_ = lean_ctor_get(v___x_2973_, 0);
                v_time_2975_ = lean_ctor_get(v___x_2973_, 1);
                v_isSharedCheck_3002_ = (!lean_is_exclusive(v___x_2973_)) as u8;
                if v_isSharedCheck_3002_ == 0 {
                    v___x_2977_ = v___x_2973_;
                    v_isShared_2978_ = v_isSharedCheck_3002_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_2975_);
                    lean_inc(v_date_2974_);
                    lean_dec(v___x_2973_);
                    v___x_2977_ = lean_box(0);
                    v_isShared_2978_ = v_isSharedCheck_3002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_2979_ = lean_ctor_get(v_tz_2966_, 0);
                v___x_2980_ = lean_int_neg(v_months_2968_);
                v___x_2981_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2974_, v___x_2980_);
                lean_dec(v___x_2980_);
                if v_isShared_2978_ == 0 {
                    lean_ctor_set(v___x_2977_, 0, v___x_2981_);
                    v___x_2983_ = v___x_2977_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2981_);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_time_2975_);
                    v___x_2983_ = v_reuseFailAlloc_3001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_2983_);
                v___x_2984_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2983_);
                v_second_2985_ = lean_ctor_get(v___x_2984_, 0);
                lean_inc(v_second_2985_);
                v_nano_2986_ = lean_ctor_get(v___x_2984_, 1);
                lean_inc(v_nano_2986_);
                lean_dec_ref(v___x_2984_);
                v___f_2987_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2987_, 0, v___x_2983_);
                v___x_2988_ = lean_int_neg(v_offset_2979_);
                v___x_2989_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2990_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2991_ = lean_int_mul(v_second_2985_, v___x_2990_);
                lean_dec(v_second_2985_);
                v___x_2992_ = lean_int_add(v___x_2991_, v_nano_2986_);
                lean_dec(v_nano_2986_);
                lean_dec(v___x_2991_);
                v___x_2993_ = lean_int_mul(v___x_2988_, v___x_2990_);
                lean_dec(v___x_2988_);
                v___x_2994_ = lean_int_add(v___x_2993_, v___x_2989_);
                lean_dec(v___x_2993_);
                v___x_2995_ = lean_int_add(v___x_2992_, v___x_2994_);
                lean_dec(v___x_2994_);
                lean_dec(v___x_2992_);
                v_tm_2996_ = l_Std_Time_Duration_ofNanoseconds(v___x_2995_);
                lean_dec(v___x_2995_);
                v___x_2997_ = lean_mk_thunk(v___f_2987_);
                if v_isShared_2972_ == 0 {
                    lean_ctor_set(v___x_2971_, 1, v___x_2997_);
                    lean_ctor_set(v___x_2971_, 0, v_tm_2996_);
                    v___x_2999_ = v___x_2971_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_tm_2996_);
                    lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2997_);
                    v___x_2999_ = v_reuseFailAlloc_3000_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subMonthsRollOver___boxed(
    mut v_tz_3005_: *mut LeanObject,
    mut v_dt_3006_: *mut LeanObject,
    mut v_months_3007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3008_: *mut LeanObject = core::ptr::null_mut();
    v_res_3008_ = l_Std_Time_DateTime_subMonthsRollOver(v_tz_3005_, v_dt_3006_, v_months_3007_);
    lean_dec(v_months_3007_);
    lean_dec_ref(v_tz_3005_);
    return v_res_3008_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addYearsRollOver___closed__0() -> *mut LeanObject {
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    v___x_3009_ = lean_unsigned_to_nat(12);
    v___x_3010_ = lean_nat_to_int(v___x_3009_);
    return v___x_3010_;
}
pub unsafe fn l_Std_Time_DateTime_addYearsRollOver(
    mut v_tz_3011_: *mut LeanObject,
    mut v_dt_3012_: *mut LeanObject,
    mut v_years_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v_offset_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_unused_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3014_ = lean_ctor_get(v_dt_3012_, 1);
                v_isSharedCheck_3049_ = (!lean_is_exclusive(v_dt_3012_)) as u8;
                if v_isSharedCheck_3049_ == 0 {
                    v_unused_3050_ = lean_ctor_get(v_dt_3012_, 0);
                    lean_dec(v_unused_3050_);
                    v___x_3016_ = v_dt_3012_;
                    v_isShared_3017_ = v_isSharedCheck_3049_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3014_);
                    lean_dec(v_dt_3012_);
                    v___x_3016_ = lean_box(0);
                    v_isShared_3017_ = v_isSharedCheck_3049_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3018_ = lean_thunk_get_own(v_date_3014_);
                lean_dec_ref(v_date_3014_);
                v_date_3019_ = lean_ctor_get(v___x_3018_, 0);
                v_time_3020_ = lean_ctor_get(v___x_3018_, 1);
                v_isSharedCheck_3048_ = (!lean_is_exclusive(v___x_3018_)) as u8;
                if v_isSharedCheck_3048_ == 0 {
                    v___x_3022_ = v___x_3018_;
                    v_isShared_3023_ = v_isSharedCheck_3048_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3020_);
                    lean_inc(v_date_3019_);
                    lean_dec(v___x_3018_);
                    v___x_3022_ = lean_box(0);
                    v_isShared_3023_ = v_isSharedCheck_3048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3024_ = lean_ctor_get(v_tz_3011_, 0);
                v___x_3025_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3026_ = lean_int_mul(v_years_3013_, v___x_3025_);
                v___x_3027_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_3019_, v___x_3026_);
                lean_dec(v___x_3026_);
                if v_isShared_3023_ == 0 {
                    lean_ctor_set(v___x_3022_, 0, v___x_3027_);
                    v___x_3029_ = v___x_3022_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3027_);
                    lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_time_3020_);
                    v___x_3029_ = v_reuseFailAlloc_3047_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3029_);
                v___x_3030_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3029_);
                v_second_3031_ = lean_ctor_get(v___x_3030_, 0);
                lean_inc(v_second_3031_);
                v_nano_3032_ = lean_ctor_get(v___x_3030_, 1);
                lean_inc(v_nano_3032_);
                lean_dec_ref(v___x_3030_);
                v___f_3033_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3033_, 0, v___x_3029_);
                v___x_3034_ = lean_int_neg(v_offset_3024_);
                v___x_3035_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3036_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3037_ = lean_int_mul(v_second_3031_, v___x_3036_);
                lean_dec(v_second_3031_);
                v___x_3038_ = lean_int_add(v___x_3037_, v_nano_3032_);
                lean_dec(v_nano_3032_);
                lean_dec(v___x_3037_);
                v___x_3039_ = lean_int_mul(v___x_3034_, v___x_3036_);
                lean_dec(v___x_3034_);
                v___x_3040_ = lean_int_add(v___x_3039_, v___x_3035_);
                lean_dec(v___x_3039_);
                v___x_3041_ = lean_int_add(v___x_3038_, v___x_3040_);
                lean_dec(v___x_3040_);
                lean_dec(v___x_3038_);
                v_tm_3042_ = l_Std_Time_Duration_ofNanoseconds(v___x_3041_);
                lean_dec(v___x_3041_);
                v___x_3043_ = lean_mk_thunk(v___f_3033_);
                if v_isShared_3017_ == 0 {
                    lean_ctor_set(v___x_3016_, 1, v___x_3043_);
                    lean_ctor_set(v___x_3016_, 0, v_tm_3042_);
                    v___x_3045_ = v___x_3016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_tm_3042_);
                    lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3043_);
                    v___x_3045_ = v_reuseFailAlloc_3046_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addYearsRollOver___boxed(
    mut v_tz_3051_: *mut LeanObject,
    mut v_dt_3052_: *mut LeanObject,
    mut v_years_3053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3054_: *mut LeanObject = core::ptr::null_mut();
    v_res_3054_ = l_Std_Time_DateTime_addYearsRollOver(v_tz_3051_, v_dt_3052_, v_years_3053_);
    lean_dec(v_years_3053_);
    lean_dec_ref(v_tz_3051_);
    return v_res_3054_;
}
pub unsafe fn l_Std_Time_DateTime_addYearsClip(
    mut v_tz_3055_: *mut LeanObject,
    mut v_dt_3056_: *mut LeanObject,
    mut v_years_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v_offset_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v_unused_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3058_ = lean_ctor_get(v_dt_3056_, 1);
                v_isSharedCheck_3093_ = (!lean_is_exclusive(v_dt_3056_)) as u8;
                if v_isSharedCheck_3093_ == 0 {
                    v_unused_3094_ = lean_ctor_get(v_dt_3056_, 0);
                    lean_dec(v_unused_3094_);
                    v___x_3060_ = v_dt_3056_;
                    v_isShared_3061_ = v_isSharedCheck_3093_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3058_);
                    lean_dec(v_dt_3056_);
                    v___x_3060_ = lean_box(0);
                    v_isShared_3061_ = v_isSharedCheck_3093_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3062_ = lean_thunk_get_own(v_date_3058_);
                lean_dec_ref(v_date_3058_);
                v_date_3063_ = lean_ctor_get(v___x_3062_, 0);
                v_time_3064_ = lean_ctor_get(v___x_3062_, 1);
                v_isSharedCheck_3092_ = (!lean_is_exclusive(v___x_3062_)) as u8;
                if v_isSharedCheck_3092_ == 0 {
                    v___x_3066_ = v___x_3062_;
                    v_isShared_3067_ = v_isSharedCheck_3092_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3064_);
                    lean_inc(v_date_3063_);
                    lean_dec(v___x_3062_);
                    v___x_3066_ = lean_box(0);
                    v_isShared_3067_ = v_isSharedCheck_3092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3068_ = lean_ctor_get(v_tz_3055_, 0);
                v___x_3069_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3070_ = lean_int_mul(v_years_3057_, v___x_3069_);
                v___x_3071_ = l_Std_Time_PlainDate_addMonthsClip(v_date_3063_, v___x_3070_);
                lean_dec(v___x_3070_);
                if v_isShared_3067_ == 0 {
                    lean_ctor_set(v___x_3066_, 0, v___x_3071_);
                    v___x_3073_ = v___x_3066_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3071_);
                    lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_time_3064_);
                    v___x_3073_ = v_reuseFailAlloc_3091_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3073_);
                v___x_3074_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3073_);
                v_second_3075_ = lean_ctor_get(v___x_3074_, 0);
                lean_inc(v_second_3075_);
                v_nano_3076_ = lean_ctor_get(v___x_3074_, 1);
                lean_inc(v_nano_3076_);
                lean_dec_ref(v___x_3074_);
                v___f_3077_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3077_, 0, v___x_3073_);
                v___x_3078_ = lean_int_neg(v_offset_3068_);
                v___x_3079_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3080_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3081_ = lean_int_mul(v_second_3075_, v___x_3080_);
                lean_dec(v_second_3075_);
                v___x_3082_ = lean_int_add(v___x_3081_, v_nano_3076_);
                lean_dec(v_nano_3076_);
                lean_dec(v___x_3081_);
                v___x_3083_ = lean_int_mul(v___x_3078_, v___x_3080_);
                lean_dec(v___x_3078_);
                v___x_3084_ = lean_int_add(v___x_3083_, v___x_3079_);
                lean_dec(v___x_3083_);
                v___x_3085_ = lean_int_add(v___x_3082_, v___x_3084_);
                lean_dec(v___x_3084_);
                lean_dec(v___x_3082_);
                v_tm_3086_ = l_Std_Time_Duration_ofNanoseconds(v___x_3085_);
                lean_dec(v___x_3085_);
                v___x_3087_ = lean_mk_thunk(v___f_3077_);
                if v_isShared_3061_ == 0 {
                    lean_ctor_set(v___x_3060_, 1, v___x_3087_);
                    lean_ctor_set(v___x_3060_, 0, v_tm_3086_);
                    v___x_3089_ = v___x_3060_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_tm_3086_);
                    lean_ctor_set(v_reuseFailAlloc_3090_, 1, v___x_3087_);
                    v___x_3089_ = v_reuseFailAlloc_3090_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3089_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_addYearsClip___boxed(
    mut v_tz_3095_: *mut LeanObject,
    mut v_dt_3096_: *mut LeanObject,
    mut v_years_3097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3098_: *mut LeanObject = core::ptr::null_mut();
    v_res_3098_ = l_Std_Time_DateTime_addYearsClip(v_tz_3095_, v_dt_3096_, v_years_3097_);
    lean_dec(v_years_3097_);
    lean_dec_ref(v_tz_3095_);
    return v_res_3098_;
}
pub unsafe fn l_Std_Time_DateTime_subYearsRollOver(
    mut v_tz_3099_: *mut LeanObject,
    mut v_dt_3100_: *mut LeanObject,
    mut v_years_3101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v_offset_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_unused_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3102_ = lean_ctor_get(v_dt_3100_, 1);
                v_isSharedCheck_3138_ = (!lean_is_exclusive(v_dt_3100_)) as u8;
                if v_isSharedCheck_3138_ == 0 {
                    v_unused_3139_ = lean_ctor_get(v_dt_3100_, 0);
                    lean_dec(v_unused_3139_);
                    v___x_3104_ = v_dt_3100_;
                    v_isShared_3105_ = v_isSharedCheck_3138_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3102_);
                    lean_dec(v_dt_3100_);
                    v___x_3104_ = lean_box(0);
                    v_isShared_3105_ = v_isSharedCheck_3138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3106_ = lean_thunk_get_own(v_date_3102_);
                lean_dec_ref(v_date_3102_);
                v_date_3107_ = lean_ctor_get(v___x_3106_, 0);
                v_time_3108_ = lean_ctor_get(v___x_3106_, 1);
                v_isSharedCheck_3137_ = (!lean_is_exclusive(v___x_3106_)) as u8;
                if v_isSharedCheck_3137_ == 0 {
                    v___x_3110_ = v___x_3106_;
                    v_isShared_3111_ = v_isSharedCheck_3137_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3108_);
                    lean_inc(v_date_3107_);
                    lean_dec(v___x_3106_);
                    v___x_3110_ = lean_box(0);
                    v_isShared_3111_ = v_isSharedCheck_3137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3112_ = lean_ctor_get(v_tz_3099_, 0);
                v___x_3113_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3114_ = lean_int_mul(v_years_3101_, v___x_3113_);
                v___x_3115_ = lean_int_neg(v___x_3114_);
                lean_dec(v___x_3114_);
                v___x_3116_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_3107_, v___x_3115_);
                lean_dec(v___x_3115_);
                if v_isShared_3111_ == 0 {
                    lean_ctor_set(v___x_3110_, 0, v___x_3116_);
                    v___x_3118_ = v___x_3110_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3116_);
                    lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_time_3108_);
                    v___x_3118_ = v_reuseFailAlloc_3136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3118_);
                v___x_3119_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3118_);
                v_second_3120_ = lean_ctor_get(v___x_3119_, 0);
                lean_inc(v_second_3120_);
                v_nano_3121_ = lean_ctor_get(v___x_3119_, 1);
                lean_inc(v_nano_3121_);
                lean_dec_ref(v___x_3119_);
                v___f_3122_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3122_, 0, v___x_3118_);
                v___x_3123_ = lean_int_neg(v_offset_3112_);
                v___x_3124_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3125_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3126_ = lean_int_mul(v_second_3120_, v___x_3125_);
                lean_dec(v_second_3120_);
                v___x_3127_ = lean_int_add(v___x_3126_, v_nano_3121_);
                lean_dec(v_nano_3121_);
                lean_dec(v___x_3126_);
                v___x_3128_ = lean_int_mul(v___x_3123_, v___x_3125_);
                lean_dec(v___x_3123_);
                v___x_3129_ = lean_int_add(v___x_3128_, v___x_3124_);
                lean_dec(v___x_3128_);
                v___x_3130_ = lean_int_add(v___x_3127_, v___x_3129_);
                lean_dec(v___x_3129_);
                lean_dec(v___x_3127_);
                v_tm_3131_ = l_Std_Time_Duration_ofNanoseconds(v___x_3130_);
                lean_dec(v___x_3130_);
                v___x_3132_ = lean_mk_thunk(v___f_3122_);
                if v_isShared_3105_ == 0 {
                    lean_ctor_set(v___x_3104_, 1, v___x_3132_);
                    lean_ctor_set(v___x_3104_, 0, v_tm_3131_);
                    v___x_3134_ = v___x_3104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_tm_3131_);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3132_);
                    v___x_3134_ = v_reuseFailAlloc_3135_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subYearsRollOver___boxed(
    mut v_tz_3140_: *mut LeanObject,
    mut v_dt_3141_: *mut LeanObject,
    mut v_years_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3143_: *mut LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Std_Time_DateTime_subYearsRollOver(v_tz_3140_, v_dt_3141_, v_years_3142_);
    lean_dec(v_years_3142_);
    lean_dec_ref(v_tz_3140_);
    return v_res_3143_;
}
pub unsafe fn l_Std_Time_DateTime_subYearsClip(
    mut v_tz_3144_: *mut LeanObject,
    mut v_dt_3145_: *mut LeanObject,
    mut v_years_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3150_: u8 = 0;
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v_offset_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_unused_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3147_ = lean_ctor_get(v_dt_3145_, 1);
                v_isSharedCheck_3183_ = (!lean_is_exclusive(v_dt_3145_)) as u8;
                if v_isSharedCheck_3183_ == 0 {
                    v_unused_3184_ = lean_ctor_get(v_dt_3145_, 0);
                    lean_dec(v_unused_3184_);
                    v___x_3149_ = v_dt_3145_;
                    v_isShared_3150_ = v_isSharedCheck_3183_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3147_);
                    lean_dec(v_dt_3145_);
                    v___x_3149_ = lean_box(0);
                    v_isShared_3150_ = v_isSharedCheck_3183_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3151_ = lean_thunk_get_own(v_date_3147_);
                lean_dec_ref(v_date_3147_);
                v_date_3152_ = lean_ctor_get(v___x_3151_, 0);
                v_time_3153_ = lean_ctor_get(v___x_3151_, 1);
                v_isSharedCheck_3182_ = (!lean_is_exclusive(v___x_3151_)) as u8;
                if v_isSharedCheck_3182_ == 0 {
                    v___x_3155_ = v___x_3151_;
                    v_isShared_3156_ = v_isSharedCheck_3182_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3153_);
                    lean_inc(v_date_3152_);
                    lean_dec(v___x_3151_);
                    v___x_3155_ = lean_box(0);
                    v_isShared_3156_ = v_isSharedCheck_3182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3157_ = lean_ctor_get(v_tz_3144_, 0);
                v___x_3158_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3159_ = lean_int_mul(v_years_3146_, v___x_3158_);
                v___x_3160_ = lean_int_neg(v___x_3159_);
                lean_dec(v___x_3159_);
                v___x_3161_ = l_Std_Time_PlainDate_addMonthsClip(v_date_3152_, v___x_3160_);
                lean_dec(v___x_3160_);
                if v_isShared_3156_ == 0 {
                    lean_ctor_set(v___x_3155_, 0, v___x_3161_);
                    v___x_3163_ = v___x_3155_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3161_);
                    lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_time_3153_);
                    v___x_3163_ = v_reuseFailAlloc_3181_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3163_);
                v___x_3164_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3163_);
                v_second_3165_ = lean_ctor_get(v___x_3164_, 0);
                lean_inc(v_second_3165_);
                v_nano_3166_ = lean_ctor_get(v___x_3164_, 1);
                lean_inc(v_nano_3166_);
                lean_dec_ref(v___x_3164_);
                v___f_3167_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3167_, 0, v___x_3163_);
                v___x_3168_ = lean_int_neg(v_offset_3157_);
                v___x_3169_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3170_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3171_ = lean_int_mul(v_second_3165_, v___x_3170_);
                lean_dec(v_second_3165_);
                v___x_3172_ = lean_int_add(v___x_3171_, v_nano_3166_);
                lean_dec(v_nano_3166_);
                lean_dec(v___x_3171_);
                v___x_3173_ = lean_int_mul(v___x_3168_, v___x_3170_);
                lean_dec(v___x_3168_);
                v___x_3174_ = lean_int_add(v___x_3173_, v___x_3169_);
                lean_dec(v___x_3173_);
                v___x_3175_ = lean_int_add(v___x_3172_, v___x_3174_);
                lean_dec(v___x_3174_);
                lean_dec(v___x_3172_);
                v_tm_3176_ = l_Std_Time_Duration_ofNanoseconds(v___x_3175_);
                lean_dec(v___x_3175_);
                v___x_3177_ = lean_mk_thunk(v___f_3167_);
                if v_isShared_3150_ == 0 {
                    lean_ctor_set(v___x_3149_, 1, v___x_3177_);
                    lean_ctor_set(v___x_3149_, 0, v_tm_3176_);
                    v___x_3179_ = v___x_3149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_tm_3176_);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3177_);
                    v___x_3179_ = v_reuseFailAlloc_3180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_subYearsClip___boxed(
    mut v_tz_3185_: *mut LeanObject,
    mut v_dt_3186_: *mut LeanObject,
    mut v_years_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3188_: *mut LeanObject = core::ptr::null_mut();
    v_res_3188_ = l_Std_Time_DateTime_subYearsClip(v_tz_3185_, v_dt_3186_, v_years_3187_);
    lean_dec(v_years_3187_);
    lean_dec_ref(v_tz_3185_);
    return v_res_3188_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withDaysClip___closed__0() -> *mut LeanObject {
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    v___x_3189_ = lean_unsigned_to_nat(4);
    v___x_3190_ = lean_nat_to_int(v___x_3189_);
    return v___x_3190_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withDaysClip___closed__1() -> *mut LeanObject {
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    v___x_3191_ = lean_unsigned_to_nat(400);
    v___x_3192_ = lean_nat_to_int(v___x_3191_);
    return v___x_3192_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withDaysClip___closed__2() -> *mut LeanObject {
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    v___x_3193_ = lean_unsigned_to_nat(100);
    v___x_3194_ = lean_nat_to_int(v___x_3193_);
    return v___x_3194_;
}
pub unsafe fn l_Std_Time_DateTime_withDaysClip(
    mut v_tz_3195_: *mut LeanObject,
    mut v_dt_3196_: *mut LeanObject,
    mut v_days_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v_offset_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v_unused_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___y_3239_: u8 = 0;
    let mut v_max_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v_isSharedCheck_3259_: u8 = 0;
    let mut v_unused_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_unused_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3198_ = lean_ctor_get(v_dt_3196_, 1);
                v_isSharedCheck_3261_ = (!lean_is_exclusive(v_dt_3196_)) as u8;
                if v_isSharedCheck_3261_ == 0 {
                    v_unused_3262_ = lean_ctor_get(v_dt_3196_, 0);
                    lean_dec(v_unused_3262_);
                    v___x_3200_ = v_dt_3196_;
                    v_isShared_3201_ = v_isSharedCheck_3261_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3198_);
                    lean_dec(v_dt_3196_);
                    v___x_3200_ = lean_box(0);
                    v_isShared_3201_ = v_isSharedCheck_3261_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3202_ = lean_thunk_get_own(v_date_3198_);
                lean_dec_ref(v_date_3198_);
                v_date_3232_ = lean_ctor_get(v___x_3202_, 0);
                lean_inc_ref(v_date_3232_);
                v_year_3233_ = lean_ctor_get(v_date_3232_, 0);
                v_month_3234_ = lean_ctor_get(v_date_3232_, 1);
                v_isSharedCheck_3259_ = (!lean_is_exclusive(v_date_3232_)) as u8;
                if v_isSharedCheck_3259_ == 0 {
                    v_unused_3260_ = lean_ctor_get(v_date_3232_, 2);
                    lean_dec(v_unused_3260_);
                    v___x_3236_ = v_date_3232_;
                    v_isShared_3237_ = v_isSharedCheck_3259_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_month_3234_);
                    lean_inc(v_year_3233_);
                    lean_dec(v_date_3232_);
                    v___x_3236_ = lean_box(0);
                    v_isShared_3237_ = v_isSharedCheck_3259_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3205_ = lean_ctor_get(v___x_3202_, 1);
                v_isSharedCheck_3230_ = (!lean_is_exclusive(v___x_3202_)) as u8;
                if v_isSharedCheck_3230_ == 0 {
                    v_unused_3231_ = lean_ctor_get(v___x_3202_, 0);
                    lean_dec(v_unused_3231_);
                    v___x_3207_ = v___x_3202_;
                    v_isShared_3208_ = v_isSharedCheck_3230_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_time_3205_);
                    lean_dec(v___x_3202_);
                    v___x_3207_ = lean_box(0);
                    v_isShared_3208_ = v_isSharedCheck_3230_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3209_ = lean_ctor_get(v_tz_3195_, 0);
                if v_isShared_3208_ == 0 {
                    lean_ctor_set(v___x_3207_, 0, v___y_3204_);
                    v___x_3211_ = v___x_3207_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___y_3204_);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_time_3205_);
                    v___x_3211_ = v_reuseFailAlloc_3229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v___x_3211_);
                v___x_3212_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3211_);
                v_second_3213_ = lean_ctor_get(v___x_3212_, 0);
                lean_inc(v_second_3213_);
                v_nano_3214_ = lean_ctor_get(v___x_3212_, 1);
                lean_inc(v_nano_3214_);
                lean_dec_ref(v___x_3212_);
                v___f_3215_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3215_, 0, v___x_3211_);
                v___x_3216_ = lean_int_neg(v_offset_3209_);
                v___x_3217_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3218_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3219_ = lean_int_mul(v_second_3213_, v___x_3218_);
                lean_dec(v_second_3213_);
                v___x_3220_ = lean_int_add(v___x_3219_, v_nano_3214_);
                lean_dec(v_nano_3214_);
                lean_dec(v___x_3219_);
                v___x_3221_ = lean_int_mul(v___x_3216_, v___x_3218_);
                lean_dec(v___x_3216_);
                v___x_3222_ = lean_int_add(v___x_3221_, v___x_3217_);
                lean_dec(v___x_3221_);
                v___x_3223_ = lean_int_add(v___x_3220_, v___x_3222_);
                lean_dec(v___x_3222_);
                lean_dec(v___x_3220_);
                v_tm_3224_ = l_Std_Time_Duration_ofNanoseconds(v___x_3223_);
                lean_dec(v___x_3223_);
                v___x_3225_ = lean_mk_thunk(v___f_3215_);
                if v_isShared_3201_ == 0 {
                    lean_ctor_set(v___x_3200_, 1, v___x_3225_);
                    lean_ctor_set(v___x_3200_, 0, v_tm_3224_);
                    v___x_3227_ = v___x_3200_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_tm_3224_);
                    lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3225_);
                    v___x_3227_ = v_reuseFailAlloc_3228_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3227_;
            }
            6 => {
                v___x_3248_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_3249_ = lean_int_mod(v_year_3233_, v___x_3248_);
                v___x_3250_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3255_ = lean_int_dec_eq(v___x_3249_, v___x_3250_);
                lean_dec(v___x_3249_);
                if v___x_3255_ == 0 {
                    v___y_3239_ = v___x_3255_;
                    state = 7;
                    continue;
                } else {
                    v___x_3256_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_3257_ = lean_int_mod(v_year_3233_, v___x_3256_);
                    v___x_3258_ = lean_int_dec_eq(v___x_3257_, v___x_3250_);
                    lean_dec(v___x_3257_);
                    if v___x_3258_ == 0 {
                        if v___x_3255_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            v___y_3239_ = v___x_3255_;
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
                v_max_3240_ = l_Std_Time_Month_Ordinal_days(v___y_3239_, v_month_3234_);
                v___x_3241_ = lean_int_dec_lt(v_max_3240_, v_days_3197_);
                if v___x_3241_ == 0 {
                    lean_dec(v_max_3240_);
                    if v_isShared_3237_ == 0 {
                        lean_ctor_set(v___x_3236_, 2, v_days_3197_);
                        v___x_3243_ = v___x_3236_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_year_3233_);
                        lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_month_3234_);
                        lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_days_3197_);
                        v___x_3243_ = v_reuseFailAlloc_3244_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_days_3197_);
                    if v_isShared_3237_ == 0 {
                        lean_ctor_set(v___x_3236_, 2, v_max_3240_);
                        v___x_3246_ = v___x_3236_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_year_3233_);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_month_3234_);
                        lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_max_3240_);
                        v___x_3246_ = v_reuseFailAlloc_3247_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_3204_ = v___x_3243_;
                state = 2;
                continue;
            }
            9 => {
                v___y_3204_ = v___x_3246_;
                state = 2;
                continue;
            }
            10 => {
                v___x_3252_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_3253_ = lean_int_mod(v_year_3233_, v___x_3252_);
                v___x_3254_ = lean_int_dec_eq(v___x_3253_, v___x_3250_);
                lean_dec(v___x_3253_);
                v___y_3239_ = v___x_3254_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withDaysClip___boxed(
    mut v_tz_3263_: *mut LeanObject,
    mut v_dt_3264_: *mut LeanObject,
    mut v_days_3265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3266_: *mut LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Std_Time_DateTime_withDaysClip(v_tz_3263_, v_dt_3264_, v_days_3265_);
    lean_dec_ref(v_tz_3263_);
    return v_res_3266_;
}
pub unsafe fn l_Std_Time_DateTime_withDaysRollOver(
    mut v_tz_3267_: *mut LeanObject,
    mut v_dt_3268_: *mut LeanObject,
    mut v_days_3269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v_year_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v_unused_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3270_ = lean_ctor_get(v_dt_3268_, 1);
                v_isSharedCheck_3305_ = (!lean_is_exclusive(v_dt_3268_)) as u8;
                if v_isSharedCheck_3305_ == 0 {
                    v_unused_3306_ = lean_ctor_get(v_dt_3268_, 0);
                    lean_dec(v_unused_3306_);
                    v___x_3272_ = v_dt_3268_;
                    v_isShared_3273_ = v_isSharedCheck_3305_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3270_);
                    lean_dec(v_dt_3268_);
                    v___x_3272_ = lean_box(0);
                    v_isShared_3273_ = v_isSharedCheck_3305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3274_ = lean_thunk_get_own(v_date_3270_);
                lean_dec_ref(v_date_3270_);
                v_date_3275_ = lean_ctor_get(v___x_3274_, 0);
                v_time_3276_ = lean_ctor_get(v___x_3274_, 1);
                v_isSharedCheck_3304_ = (!lean_is_exclusive(v___x_3274_)) as u8;
                if v_isSharedCheck_3304_ == 0 {
                    v___x_3278_ = v___x_3274_;
                    v_isShared_3279_ = v_isSharedCheck_3304_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3276_);
                    lean_inc(v_date_3275_);
                    lean_dec(v___x_3274_);
                    v___x_3278_ = lean_box(0);
                    v_isShared_3279_ = v_isSharedCheck_3304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3280_ = lean_ctor_get(v_date_3275_, 0);
                lean_inc(v_year_3280_);
                v_month_3281_ = lean_ctor_get(v_date_3275_, 1);
                lean_inc(v_month_3281_);
                lean_dec_ref(v_date_3275_);
                v_offset_3282_ = lean_ctor_get(v_tz_3267_, 0);
                v___x_3283_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3280_, v_month_3281_, v_days_3269_);
                if v_isShared_3279_ == 0 {
                    lean_ctor_set(v___x_3278_, 0, v___x_3283_);
                    v___x_3285_ = v___x_3278_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3283_);
                    lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_time_3276_);
                    v___x_3285_ = v_reuseFailAlloc_3303_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3285_);
                v___x_3286_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3285_);
                v_second_3287_ = lean_ctor_get(v___x_3286_, 0);
                lean_inc(v_second_3287_);
                v_nano_3288_ = lean_ctor_get(v___x_3286_, 1);
                lean_inc(v_nano_3288_);
                lean_dec_ref(v___x_3286_);
                v___f_3289_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3289_, 0, v___x_3285_);
                v___x_3290_ = lean_int_neg(v_offset_3282_);
                v___x_3291_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3292_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3293_ = lean_int_mul(v_second_3287_, v___x_3292_);
                lean_dec(v_second_3287_);
                v___x_3294_ = lean_int_add(v___x_3293_, v_nano_3288_);
                lean_dec(v_nano_3288_);
                lean_dec(v___x_3293_);
                v___x_3295_ = lean_int_mul(v___x_3290_, v___x_3292_);
                lean_dec(v___x_3290_);
                v___x_3296_ = lean_int_add(v___x_3295_, v___x_3291_);
                lean_dec(v___x_3295_);
                v___x_3297_ = lean_int_add(v___x_3294_, v___x_3296_);
                lean_dec(v___x_3296_);
                lean_dec(v___x_3294_);
                v_tm_3298_ = l_Std_Time_Duration_ofNanoseconds(v___x_3297_);
                lean_dec(v___x_3297_);
                v___x_3299_ = lean_mk_thunk(v___f_3289_);
                if v_isShared_3273_ == 0 {
                    lean_ctor_set(v___x_3272_, 1, v___x_3299_);
                    lean_ctor_set(v___x_3272_, 0, v_tm_3298_);
                    v___x_3301_ = v___x_3272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_tm_3298_);
                    lean_ctor_set(v_reuseFailAlloc_3302_, 1, v___x_3299_);
                    v___x_3301_ = v_reuseFailAlloc_3302_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3301_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withDaysRollOver___boxed(
    mut v_tz_3307_: *mut LeanObject,
    mut v_dt_3308_: *mut LeanObject,
    mut v_days_3309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3310_: *mut LeanObject = core::ptr::null_mut();
    v_res_3310_ = l_Std_Time_DateTime_withDaysRollOver(v_tz_3307_, v_dt_3308_, v_days_3309_);
    lean_dec(v_days_3309_);
    lean_dec_ref(v_tz_3307_);
    return v_res_3310_;
}
pub unsafe fn l_Std_Time_DateTime_withMonthClip(
    mut v_tz_3311_: *mut LeanObject,
    mut v_dt_3312_: *mut LeanObject,
    mut v_month_3313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v_offset_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3353_: u8 = 0;
    let mut v___y_3355_: u8 = 0;
    let mut v_max_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u8 = 0;
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v_unused_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut v_unused_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3314_ = lean_ctor_get(v_dt_3312_, 1);
                v_isSharedCheck_3377_ = (!lean_is_exclusive(v_dt_3312_)) as u8;
                if v_isSharedCheck_3377_ == 0 {
                    v_unused_3378_ = lean_ctor_get(v_dt_3312_, 0);
                    lean_dec(v_unused_3378_);
                    v___x_3316_ = v_dt_3312_;
                    v_isShared_3317_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3314_);
                    lean_dec(v_dt_3312_);
                    v___x_3316_ = lean_box(0);
                    v_isShared_3317_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3318_ = lean_thunk_get_own(v_date_3314_);
                lean_dec_ref(v_date_3314_);
                v_date_3348_ = lean_ctor_get(v___x_3318_, 0);
                lean_inc_ref(v_date_3348_);
                v_year_3349_ = lean_ctor_get(v_date_3348_, 0);
                v_day_3350_ = lean_ctor_get(v_date_3348_, 2);
                v_isSharedCheck_3375_ = (!lean_is_exclusive(v_date_3348_)) as u8;
                if v_isSharedCheck_3375_ == 0 {
                    v_unused_3376_ = lean_ctor_get(v_date_3348_, 1);
                    lean_dec(v_unused_3376_);
                    v___x_3352_ = v_date_3348_;
                    v_isShared_3353_ = v_isSharedCheck_3375_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_day_3350_);
                    lean_inc(v_year_3349_);
                    lean_dec(v_date_3348_);
                    v___x_3352_ = lean_box(0);
                    v_isShared_3353_ = v_isSharedCheck_3375_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3321_ = lean_ctor_get(v___x_3318_, 1);
                v_isSharedCheck_3346_ = (!lean_is_exclusive(v___x_3318_)) as u8;
                if v_isSharedCheck_3346_ == 0 {
                    v_unused_3347_ = lean_ctor_get(v___x_3318_, 0);
                    lean_dec(v_unused_3347_);
                    v___x_3323_ = v___x_3318_;
                    v_isShared_3324_ = v_isSharedCheck_3346_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_time_3321_);
                    lean_dec(v___x_3318_);
                    v___x_3323_ = lean_box(0);
                    v_isShared_3324_ = v_isSharedCheck_3346_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3325_ = lean_ctor_get(v_tz_3311_, 0);
                if v_isShared_3324_ == 0 {
                    lean_ctor_set(v___x_3323_, 0, v___y_3320_);
                    v___x_3327_ = v___x_3323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___y_3320_);
                    lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_time_3321_);
                    v___x_3327_ = v_reuseFailAlloc_3345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v___x_3327_);
                v___x_3328_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3327_);
                v_second_3329_ = lean_ctor_get(v___x_3328_, 0);
                lean_inc(v_second_3329_);
                v_nano_3330_ = lean_ctor_get(v___x_3328_, 1);
                lean_inc(v_nano_3330_);
                lean_dec_ref(v___x_3328_);
                v___f_3331_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3331_, 0, v___x_3327_);
                v___x_3332_ = lean_int_neg(v_offset_3325_);
                v___x_3333_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3334_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3335_ = lean_int_mul(v_second_3329_, v___x_3334_);
                lean_dec(v_second_3329_);
                v___x_3336_ = lean_int_add(v___x_3335_, v_nano_3330_);
                lean_dec(v_nano_3330_);
                lean_dec(v___x_3335_);
                v___x_3337_ = lean_int_mul(v___x_3332_, v___x_3334_);
                lean_dec(v___x_3332_);
                v___x_3338_ = lean_int_add(v___x_3337_, v___x_3333_);
                lean_dec(v___x_3337_);
                v___x_3339_ = lean_int_add(v___x_3336_, v___x_3338_);
                lean_dec(v___x_3338_);
                lean_dec(v___x_3336_);
                v_tm_3340_ = l_Std_Time_Duration_ofNanoseconds(v___x_3339_);
                lean_dec(v___x_3339_);
                v___x_3341_ = lean_mk_thunk(v___f_3331_);
                if v_isShared_3317_ == 0 {
                    lean_ctor_set(v___x_3316_, 1, v___x_3341_);
                    lean_ctor_set(v___x_3316_, 0, v_tm_3340_);
                    v___x_3343_ = v___x_3316_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_tm_3340_);
                    lean_ctor_set(v_reuseFailAlloc_3344_, 1, v___x_3341_);
                    v___x_3343_ = v_reuseFailAlloc_3344_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3343_;
            }
            6 => {
                v___x_3364_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_3365_ = lean_int_mod(v_year_3349_, v___x_3364_);
                v___x_3366_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3371_ = lean_int_dec_eq(v___x_3365_, v___x_3366_);
                lean_dec(v___x_3365_);
                if v___x_3371_ == 0 {
                    v___y_3355_ = v___x_3371_;
                    state = 7;
                    continue;
                } else {
                    v___x_3372_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_3373_ = lean_int_mod(v_year_3349_, v___x_3372_);
                    v___x_3374_ = lean_int_dec_eq(v___x_3373_, v___x_3366_);
                    lean_dec(v___x_3373_);
                    if v___x_3374_ == 0 {
                        if v___x_3371_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            v___y_3355_ = v___x_3371_;
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
                v_max_3356_ = l_Std_Time_Month_Ordinal_days(v___y_3355_, v_month_3313_);
                v___x_3357_ = lean_int_dec_lt(v_max_3356_, v_day_3350_);
                if v___x_3357_ == 0 {
                    lean_dec(v_max_3356_);
                    if v_isShared_3353_ == 0 {
                        lean_ctor_set(v___x_3352_, 1, v_month_3313_);
                        v___x_3359_ = v___x_3352_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_year_3349_);
                        lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_month_3313_);
                        lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_day_3350_);
                        v___x_3359_ = v_reuseFailAlloc_3360_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_day_3350_);
                    if v_isShared_3353_ == 0 {
                        lean_ctor_set(v___x_3352_, 2, v_max_3356_);
                        lean_ctor_set(v___x_3352_, 1, v_month_3313_);
                        v___x_3362_ = v___x_3352_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_year_3349_);
                        lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_month_3313_);
                        lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_max_3356_);
                        v___x_3362_ = v_reuseFailAlloc_3363_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_3320_ = v___x_3359_;
                state = 2;
                continue;
            }
            9 => {
                v___y_3320_ = v___x_3362_;
                state = 2;
                continue;
            }
            10 => {
                v___x_3368_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_3369_ = lean_int_mod(v_year_3349_, v___x_3368_);
                v___x_3370_ = lean_int_dec_eq(v___x_3369_, v___x_3366_);
                lean_dec(v___x_3369_);
                v___y_3355_ = v___x_3370_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withMonthClip___boxed(
    mut v_tz_3379_: *mut LeanObject,
    mut v_dt_3380_: *mut LeanObject,
    mut v_month_3381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3382_: *mut LeanObject = core::ptr::null_mut();
    v_res_3382_ = l_Std_Time_DateTime_withMonthClip(v_tz_3379_, v_dt_3380_, v_month_3381_);
    lean_dec_ref(v_tz_3379_);
    return v_res_3382_;
}
pub unsafe fn l_Std_Time_DateTime_withMonthRollOver(
    mut v_tz_3383_: *mut LeanObject,
    mut v_dt_3384_: *mut LeanObject,
    mut v_month_3385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v_year_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut v_isSharedCheck_3421_: u8 = 0;
    let mut v_unused_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3386_ = lean_ctor_get(v_dt_3384_, 1);
                v_isSharedCheck_3421_ = (!lean_is_exclusive(v_dt_3384_)) as u8;
                if v_isSharedCheck_3421_ == 0 {
                    v_unused_3422_ = lean_ctor_get(v_dt_3384_, 0);
                    lean_dec(v_unused_3422_);
                    v___x_3388_ = v_dt_3384_;
                    v_isShared_3389_ = v_isSharedCheck_3421_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3386_);
                    lean_dec(v_dt_3384_);
                    v___x_3388_ = lean_box(0);
                    v_isShared_3389_ = v_isSharedCheck_3421_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3390_ = lean_thunk_get_own(v_date_3386_);
                lean_dec_ref(v_date_3386_);
                v_date_3391_ = lean_ctor_get(v___x_3390_, 0);
                v_time_3392_ = lean_ctor_get(v___x_3390_, 1);
                v_isSharedCheck_3420_ = (!lean_is_exclusive(v___x_3390_)) as u8;
                if v_isSharedCheck_3420_ == 0 {
                    v___x_3394_ = v___x_3390_;
                    v_isShared_3395_ = v_isSharedCheck_3420_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3392_);
                    lean_inc(v_date_3391_);
                    lean_dec(v___x_3390_);
                    v___x_3394_ = lean_box(0);
                    v_isShared_3395_ = v_isSharedCheck_3420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3396_ = lean_ctor_get(v_date_3391_, 0);
                lean_inc(v_year_3396_);
                v_day_3397_ = lean_ctor_get(v_date_3391_, 2);
                lean_inc(v_day_3397_);
                lean_dec_ref(v_date_3391_);
                v_offset_3398_ = lean_ctor_get(v_tz_3383_, 0);
                v___x_3399_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3396_, v_month_3385_, v_day_3397_);
                lean_dec(v_day_3397_);
                if v_isShared_3395_ == 0 {
                    lean_ctor_set(v___x_3394_, 0, v___x_3399_);
                    v___x_3401_ = v___x_3394_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3399_);
                    lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_time_3392_);
                    v___x_3401_ = v_reuseFailAlloc_3419_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3401_);
                v___x_3402_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3401_);
                v_second_3403_ = lean_ctor_get(v___x_3402_, 0);
                lean_inc(v_second_3403_);
                v_nano_3404_ = lean_ctor_get(v___x_3402_, 1);
                lean_inc(v_nano_3404_);
                lean_dec_ref(v___x_3402_);
                v___f_3405_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3405_, 0, v___x_3401_);
                v___x_3406_ = lean_int_neg(v_offset_3398_);
                v___x_3407_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3408_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3409_ = lean_int_mul(v_second_3403_, v___x_3408_);
                lean_dec(v_second_3403_);
                v___x_3410_ = lean_int_add(v___x_3409_, v_nano_3404_);
                lean_dec(v_nano_3404_);
                lean_dec(v___x_3409_);
                v___x_3411_ = lean_int_mul(v___x_3406_, v___x_3408_);
                lean_dec(v___x_3406_);
                v___x_3412_ = lean_int_add(v___x_3411_, v___x_3407_);
                lean_dec(v___x_3411_);
                v___x_3413_ = lean_int_add(v___x_3410_, v___x_3412_);
                lean_dec(v___x_3412_);
                lean_dec(v___x_3410_);
                v_tm_3414_ = l_Std_Time_Duration_ofNanoseconds(v___x_3413_);
                lean_dec(v___x_3413_);
                v___x_3415_ = lean_mk_thunk(v___f_3405_);
                if v_isShared_3389_ == 0 {
                    lean_ctor_set(v___x_3388_, 1, v___x_3415_);
                    lean_ctor_set(v___x_3388_, 0, v_tm_3414_);
                    v___x_3417_ = v___x_3388_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3418_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_tm_3414_);
                    lean_ctor_set(v_reuseFailAlloc_3418_, 1, v___x_3415_);
                    v___x_3417_ = v_reuseFailAlloc_3418_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3417_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withMonthRollOver___boxed(
    mut v_tz_3423_: *mut LeanObject,
    mut v_dt_3424_: *mut LeanObject,
    mut v_month_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3426_: *mut LeanObject = core::ptr::null_mut();
    v_res_3426_ = l_Std_Time_DateTime_withMonthRollOver(v_tz_3423_, v_dt_3424_, v_month_3425_);
    lean_dec_ref(v_tz_3423_);
    return v_res_3426_;
}
pub unsafe fn l_Std_Time_DateTime_withYearClip(
    mut v_tz_3427_: *mut LeanObject,
    mut v_dt_3428_: *mut LeanObject,
    mut v_year_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v_offset_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_unused_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___y_3471_: u8 = 0;
    let mut v_max_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: u8 = 0;
    let mut v___x_3487_: u8 = 0;
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v_isSharedCheck_3491_: u8 = 0;
    let mut v_unused_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut v_unused_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3430_ = lean_ctor_get(v_dt_3428_, 1);
                v_isSharedCheck_3493_ = (!lean_is_exclusive(v_dt_3428_)) as u8;
                if v_isSharedCheck_3493_ == 0 {
                    v_unused_3494_ = lean_ctor_get(v_dt_3428_, 0);
                    lean_dec(v_unused_3494_);
                    v___x_3432_ = v_dt_3428_;
                    v_isShared_3433_ = v_isSharedCheck_3493_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3430_);
                    lean_dec(v_dt_3428_);
                    v___x_3432_ = lean_box(0);
                    v_isShared_3433_ = v_isSharedCheck_3493_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3434_ = lean_thunk_get_own(v_date_3430_);
                lean_dec_ref(v_date_3430_);
                v_date_3464_ = lean_ctor_get(v___x_3434_, 0);
                lean_inc_ref(v_date_3464_);
                v_month_3465_ = lean_ctor_get(v_date_3464_, 1);
                v_day_3466_ = lean_ctor_get(v_date_3464_, 2);
                v_isSharedCheck_3491_ = (!lean_is_exclusive(v_date_3464_)) as u8;
                if v_isSharedCheck_3491_ == 0 {
                    v_unused_3492_ = lean_ctor_get(v_date_3464_, 0);
                    lean_dec(v_unused_3492_);
                    v___x_3468_ = v_date_3464_;
                    v_isShared_3469_ = v_isSharedCheck_3491_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_day_3466_);
                    lean_inc(v_month_3465_);
                    lean_dec(v_date_3464_);
                    v___x_3468_ = lean_box(0);
                    v_isShared_3469_ = v_isSharedCheck_3491_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3437_ = lean_ctor_get(v___x_3434_, 1);
                v_isSharedCheck_3462_ = (!lean_is_exclusive(v___x_3434_)) as u8;
                if v_isSharedCheck_3462_ == 0 {
                    v_unused_3463_ = lean_ctor_get(v___x_3434_, 0);
                    lean_dec(v_unused_3463_);
                    v___x_3439_ = v___x_3434_;
                    v_isShared_3440_ = v_isSharedCheck_3462_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_time_3437_);
                    lean_dec(v___x_3434_);
                    v___x_3439_ = lean_box(0);
                    v_isShared_3440_ = v_isSharedCheck_3462_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3441_ = lean_ctor_get(v_tz_3427_, 0);
                if v_isShared_3440_ == 0 {
                    lean_ctor_set(v___x_3439_, 0, v___y_3436_);
                    v___x_3443_ = v___x_3439_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___y_3436_);
                    lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_time_3437_);
                    v___x_3443_ = v_reuseFailAlloc_3461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc_ref(v___x_3443_);
                v___x_3444_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3443_);
                v_second_3445_ = lean_ctor_get(v___x_3444_, 0);
                lean_inc(v_second_3445_);
                v_nano_3446_ = lean_ctor_get(v___x_3444_, 1);
                lean_inc(v_nano_3446_);
                lean_dec_ref(v___x_3444_);
                v___f_3447_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3447_, 0, v___x_3443_);
                v___x_3448_ = lean_int_neg(v_offset_3441_);
                v___x_3449_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3450_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3451_ = lean_int_mul(v_second_3445_, v___x_3450_);
                lean_dec(v_second_3445_);
                v___x_3452_ = lean_int_add(v___x_3451_, v_nano_3446_);
                lean_dec(v_nano_3446_);
                lean_dec(v___x_3451_);
                v___x_3453_ = lean_int_mul(v___x_3448_, v___x_3450_);
                lean_dec(v___x_3448_);
                v___x_3454_ = lean_int_add(v___x_3453_, v___x_3449_);
                lean_dec(v___x_3453_);
                v___x_3455_ = lean_int_add(v___x_3452_, v___x_3454_);
                lean_dec(v___x_3454_);
                lean_dec(v___x_3452_);
                v_tm_3456_ = l_Std_Time_Duration_ofNanoseconds(v___x_3455_);
                lean_dec(v___x_3455_);
                v___x_3457_ = lean_mk_thunk(v___f_3447_);
                if v_isShared_3433_ == 0 {
                    lean_ctor_set(v___x_3432_, 1, v___x_3457_);
                    lean_ctor_set(v___x_3432_, 0, v_tm_3456_);
                    v___x_3459_ = v___x_3432_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_tm_3456_);
                    lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3457_);
                    v___x_3459_ = v_reuseFailAlloc_3460_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3459_;
            }
            6 => {
                v___x_3480_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_3481_ = lean_int_mod(v_year_3429_, v___x_3480_);
                v___x_3482_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3487_ = lean_int_dec_eq(v___x_3481_, v___x_3482_);
                lean_dec(v___x_3481_);
                if v___x_3487_ == 0 {
                    v___y_3471_ = v___x_3487_;
                    state = 7;
                    continue;
                } else {
                    v___x_3488_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_3489_ = lean_int_mod(v_year_3429_, v___x_3488_);
                    v___x_3490_ = lean_int_dec_eq(v___x_3489_, v___x_3482_);
                    lean_dec(v___x_3489_);
                    if v___x_3490_ == 0 {
                        if v___x_3487_ == 0 {
                            state = 10;
                            continue;
                        } else {
                            v___y_3471_ = v___x_3487_;
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
                v_max_3472_ = l_Std_Time_Month_Ordinal_days(v___y_3471_, v_month_3465_);
                v___x_3473_ = lean_int_dec_lt(v_max_3472_, v_day_3466_);
                if v___x_3473_ == 0 {
                    lean_dec(v_max_3472_);
                    if v_isShared_3469_ == 0 {
                        lean_ctor_set(v___x_3468_, 0, v_year_3429_);
                        v___x_3475_ = v___x_3468_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_year_3429_);
                        lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_month_3465_);
                        lean_ctor_set(v_reuseFailAlloc_3476_, 2, v_day_3466_);
                        v___x_3475_ = v_reuseFailAlloc_3476_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_day_3466_);
                    if v_isShared_3469_ == 0 {
                        lean_ctor_set(v___x_3468_, 2, v_max_3472_);
                        lean_ctor_set(v___x_3468_, 0, v_year_3429_);
                        v___x_3478_ = v___x_3468_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_year_3429_);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_month_3465_);
                        lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_max_3472_);
                        v___x_3478_ = v_reuseFailAlloc_3479_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                v___y_3436_ = v___x_3475_;
                state = 2;
                continue;
            }
            9 => {
                v___y_3436_ = v___x_3478_;
                state = 2;
                continue;
            }
            10 => {
                v___x_3484_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_3485_ = lean_int_mod(v_year_3429_, v___x_3484_);
                v___x_3486_ = lean_int_dec_eq(v___x_3485_, v___x_3482_);
                lean_dec(v___x_3485_);
                v___y_3471_ = v___x_3486_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withYearClip___boxed(
    mut v_tz_3495_: *mut LeanObject,
    mut v_dt_3496_: *mut LeanObject,
    mut v_year_3497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3498_: *mut LeanObject = core::ptr::null_mut();
    v_res_3498_ = l_Std_Time_DateTime_withYearClip(v_tz_3495_, v_dt_3496_, v_year_3497_);
    lean_dec_ref(v_tz_3495_);
    return v_res_3498_;
}
pub unsafe fn l_Std_Time_DateTime_withYearRollOver(
    mut v_tz_3499_: *mut LeanObject,
    mut v_dt_3500_: *mut LeanObject,
    mut v_year_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v_month_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v_unused_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3502_ = lean_ctor_get(v_dt_3500_, 1);
                v_isSharedCheck_3537_ = (!lean_is_exclusive(v_dt_3500_)) as u8;
                if v_isSharedCheck_3537_ == 0 {
                    v_unused_3538_ = lean_ctor_get(v_dt_3500_, 0);
                    lean_dec(v_unused_3538_);
                    v___x_3504_ = v_dt_3500_;
                    v_isShared_3505_ = v_isSharedCheck_3537_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3502_);
                    lean_dec(v_dt_3500_);
                    v___x_3504_ = lean_box(0);
                    v_isShared_3505_ = v_isSharedCheck_3537_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3506_ = lean_thunk_get_own(v_date_3502_);
                lean_dec_ref(v_date_3502_);
                v_date_3507_ = lean_ctor_get(v___x_3506_, 0);
                v_time_3508_ = lean_ctor_get(v___x_3506_, 1);
                v_isSharedCheck_3536_ = (!lean_is_exclusive(v___x_3506_)) as u8;
                if v_isSharedCheck_3536_ == 0 {
                    v___x_3510_ = v___x_3506_;
                    v_isShared_3511_ = v_isSharedCheck_3536_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3508_);
                    lean_inc(v_date_3507_);
                    lean_dec(v___x_3506_);
                    v___x_3510_ = lean_box(0);
                    v_isShared_3511_ = v_isSharedCheck_3536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_3512_ = lean_ctor_get(v_date_3507_, 1);
                lean_inc(v_month_3512_);
                v_day_3513_ = lean_ctor_get(v_date_3507_, 2);
                lean_inc(v_day_3513_);
                lean_dec_ref(v_date_3507_);
                v_offset_3514_ = lean_ctor_get(v_tz_3499_, 0);
                v___x_3515_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3501_, v_month_3512_, v_day_3513_);
                lean_dec(v_day_3513_);
                if v_isShared_3511_ == 0 {
                    lean_ctor_set(v___x_3510_, 0, v___x_3515_);
                    v___x_3517_ = v___x_3510_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3515_);
                    lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_time_3508_);
                    v___x_3517_ = v_reuseFailAlloc_3535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v___x_3517_);
                v___x_3518_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3517_);
                v_second_3519_ = lean_ctor_get(v___x_3518_, 0);
                lean_inc(v_second_3519_);
                v_nano_3520_ = lean_ctor_get(v___x_3518_, 1);
                lean_inc(v_nano_3520_);
                lean_dec_ref(v___x_3518_);
                v___f_3521_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3521_, 0, v___x_3517_);
                v___x_3522_ = lean_int_neg(v_offset_3514_);
                v___x_3523_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3524_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3525_ = lean_int_mul(v_second_3519_, v___x_3524_);
                lean_dec(v_second_3519_);
                v___x_3526_ = lean_int_add(v___x_3525_, v_nano_3520_);
                lean_dec(v_nano_3520_);
                lean_dec(v___x_3525_);
                v___x_3527_ = lean_int_mul(v___x_3522_, v___x_3524_);
                lean_dec(v___x_3522_);
                v___x_3528_ = lean_int_add(v___x_3527_, v___x_3523_);
                lean_dec(v___x_3527_);
                v___x_3529_ = lean_int_add(v___x_3526_, v___x_3528_);
                lean_dec(v___x_3528_);
                lean_dec(v___x_3526_);
                v_tm_3530_ = l_Std_Time_Duration_ofNanoseconds(v___x_3529_);
                lean_dec(v___x_3529_);
                v___x_3531_ = lean_mk_thunk(v___f_3521_);
                if v_isShared_3505_ == 0 {
                    lean_ctor_set(v___x_3504_, 1, v___x_3531_);
                    lean_ctor_set(v___x_3504_, 0, v_tm_3530_);
                    v___x_3533_ = v___x_3504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_tm_3530_);
                    lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3531_);
                    v___x_3533_ = v_reuseFailAlloc_3534_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3533_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withYearRollOver___boxed(
    mut v_tz_3539_: *mut LeanObject,
    mut v_dt_3540_: *mut LeanObject,
    mut v_year_3541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3542_: *mut LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Std_Time_DateTime_withYearRollOver(v_tz_3539_, v_dt_3540_, v_year_3541_);
    lean_dec_ref(v_tz_3539_);
    return v_res_3542_;
}
pub unsafe fn l_Std_Time_DateTime_withHours(
    mut v_tz_3543_: *mut LeanObject,
    mut v_dt_3544_: *mut LeanObject,
    mut v_hour_3545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3549_: u8 = 0;
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v_minute_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3561_: u8 = 0;
    let mut v_offset_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut v_unused_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_unused_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3546_ = lean_ctor_get(v_dt_3544_, 1);
                v_isSharedCheck_3589_ = (!lean_is_exclusive(v_dt_3544_)) as u8;
                if v_isSharedCheck_3589_ == 0 {
                    v_unused_3590_ = lean_ctor_get(v_dt_3544_, 0);
                    lean_dec(v_unused_3590_);
                    v___x_3548_ = v_dt_3544_;
                    v_isShared_3549_ = v_isSharedCheck_3589_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3546_);
                    lean_dec(v_dt_3544_);
                    v___x_3548_ = lean_box(0);
                    v_isShared_3549_ = v_isSharedCheck_3589_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3550_ = lean_thunk_get_own(v_date_3546_);
                lean_dec_ref(v_date_3546_);
                v_time_3551_ = lean_ctor_get(v___x_3550_, 1);
                v_date_3552_ = lean_ctor_get(v___x_3550_, 0);
                v_isSharedCheck_3588_ = (!lean_is_exclusive(v___x_3550_)) as u8;
                if v_isSharedCheck_3588_ == 0 {
                    v___x_3554_ = v___x_3550_;
                    v_isShared_3555_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3551_);
                    lean_inc(v_date_3552_);
                    lean_dec(v___x_3550_);
                    v___x_3554_ = lean_box(0);
                    v_isShared_3555_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_minute_3556_ = lean_ctor_get(v_time_3551_, 1);
                v_second_3557_ = lean_ctor_get(v_time_3551_, 2);
                v_nanosecond_3558_ = lean_ctor_get(v_time_3551_, 3);
                v_isSharedCheck_3586_ = (!lean_is_exclusive(v_time_3551_)) as u8;
                if v_isSharedCheck_3586_ == 0 {
                    v_unused_3587_ = lean_ctor_get(v_time_3551_, 0);
                    lean_dec(v_unused_3587_);
                    v___x_3560_ = v_time_3551_;
                    v_isShared_3561_ = v_isSharedCheck_3586_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_3558_);
                    lean_inc(v_second_3557_);
                    lean_inc(v_minute_3556_);
                    lean_dec(v_time_3551_);
                    v___x_3560_ = lean_box(0);
                    v_isShared_3561_ = v_isSharedCheck_3586_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3562_ = lean_ctor_get(v_tz_3543_, 0);
                if v_isShared_3561_ == 0 {
                    lean_ctor_set(v___x_3560_, 0, v_hour_3545_);
                    v___x_3564_ = v___x_3560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_hour_3545_);
                    lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_minute_3556_);
                    lean_ctor_set(v_reuseFailAlloc_3585_, 2, v_second_3557_);
                    lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_nanosecond_3558_);
                    v___x_3564_ = v_reuseFailAlloc_3585_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3555_ == 0 {
                    lean_ctor_set(v___x_3554_, 1, v___x_3564_);
                    v___x_3566_ = v___x_3554_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_date_3552_);
                    lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3564_);
                    v___x_3566_ = v_reuseFailAlloc_3584_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3566_);
                v___x_3567_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3566_);
                v_second_3568_ = lean_ctor_get(v___x_3567_, 0);
                lean_inc(v_second_3568_);
                v_nano_3569_ = lean_ctor_get(v___x_3567_, 1);
                lean_inc(v_nano_3569_);
                lean_dec_ref(v___x_3567_);
                v___f_3570_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3570_, 0, v___x_3566_);
                v___x_3571_ = lean_int_neg(v_offset_3562_);
                v___x_3572_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3573_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3574_ = lean_int_mul(v_second_3568_, v___x_3573_);
                lean_dec(v_second_3568_);
                v___x_3575_ = lean_int_add(v___x_3574_, v_nano_3569_);
                lean_dec(v_nano_3569_);
                lean_dec(v___x_3574_);
                v___x_3576_ = lean_int_mul(v___x_3571_, v___x_3573_);
                lean_dec(v___x_3571_);
                v___x_3577_ = lean_int_add(v___x_3576_, v___x_3572_);
                lean_dec(v___x_3576_);
                v___x_3578_ = lean_int_add(v___x_3575_, v___x_3577_);
                lean_dec(v___x_3577_);
                lean_dec(v___x_3575_);
                v_tm_3579_ = l_Std_Time_Duration_ofNanoseconds(v___x_3578_);
                lean_dec(v___x_3578_);
                v___x_3580_ = lean_mk_thunk(v___f_3570_);
                if v_isShared_3549_ == 0 {
                    lean_ctor_set(v___x_3548_, 1, v___x_3580_);
                    lean_ctor_set(v___x_3548_, 0, v_tm_3579_);
                    v___x_3582_ = v___x_3548_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_tm_3579_);
                    lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___x_3580_);
                    v___x_3582_ = v_reuseFailAlloc_3583_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withHours___boxed(
    mut v_tz_3591_: *mut LeanObject,
    mut v_dt_3592_: *mut LeanObject,
    mut v_hour_3593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3594_: *mut LeanObject = core::ptr::null_mut();
    v_res_3594_ = l_Std_Time_DateTime_withHours(v_tz_3591_, v_dt_3592_, v_hour_3593_);
    lean_dec_ref(v_tz_3591_);
    return v_res_3594_;
}
pub unsafe fn l_Std_Time_DateTime_withMinutes(
    mut v_tz_3595_: *mut LeanObject,
    mut v_dt_3596_: *mut LeanObject,
    mut v_minute_3597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3607_: u8 = 0;
    let mut v_hour_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3613_: u8 = 0;
    let mut v_offset_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_unused_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v_unused_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3598_ = lean_ctor_get(v_dt_3596_, 1);
                v_isSharedCheck_3641_ = (!lean_is_exclusive(v_dt_3596_)) as u8;
                if v_isSharedCheck_3641_ == 0 {
                    v_unused_3642_ = lean_ctor_get(v_dt_3596_, 0);
                    lean_dec(v_unused_3642_);
                    v___x_3600_ = v_dt_3596_;
                    v_isShared_3601_ = v_isSharedCheck_3641_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3598_);
                    lean_dec(v_dt_3596_);
                    v___x_3600_ = lean_box(0);
                    v_isShared_3601_ = v_isSharedCheck_3641_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3602_ = lean_thunk_get_own(v_date_3598_);
                lean_dec_ref(v_date_3598_);
                v_time_3603_ = lean_ctor_get(v___x_3602_, 1);
                v_date_3604_ = lean_ctor_get(v___x_3602_, 0);
                v_isSharedCheck_3640_ = (!lean_is_exclusive(v___x_3602_)) as u8;
                if v_isSharedCheck_3640_ == 0 {
                    v___x_3606_ = v___x_3602_;
                    v_isShared_3607_ = v_isSharedCheck_3640_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3603_);
                    lean_inc(v_date_3604_);
                    lean_dec(v___x_3602_);
                    v___x_3606_ = lean_box(0);
                    v_isShared_3607_ = v_isSharedCheck_3640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3608_ = lean_ctor_get(v_time_3603_, 0);
                v_second_3609_ = lean_ctor_get(v_time_3603_, 2);
                v_nanosecond_3610_ = lean_ctor_get(v_time_3603_, 3);
                v_isSharedCheck_3638_ = (!lean_is_exclusive(v_time_3603_)) as u8;
                if v_isSharedCheck_3638_ == 0 {
                    v_unused_3639_ = lean_ctor_get(v_time_3603_, 1);
                    lean_dec(v_unused_3639_);
                    v___x_3612_ = v_time_3603_;
                    v_isShared_3613_ = v_isSharedCheck_3638_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_3610_);
                    lean_inc(v_second_3609_);
                    lean_inc(v_hour_3608_);
                    lean_dec(v_time_3603_);
                    v___x_3612_ = lean_box(0);
                    v_isShared_3613_ = v_isSharedCheck_3638_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3614_ = lean_ctor_get(v_tz_3595_, 0);
                if v_isShared_3613_ == 0 {
                    lean_ctor_set(v___x_3612_, 1, v_minute_3597_);
                    v___x_3616_ = v___x_3612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_hour_3608_);
                    lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_minute_3597_);
                    lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_second_3609_);
                    lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_nanosecond_3610_);
                    v___x_3616_ = v_reuseFailAlloc_3637_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3607_ == 0 {
                    lean_ctor_set(v___x_3606_, 1, v___x_3616_);
                    v___x_3618_ = v___x_3606_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_date_3604_);
                    lean_ctor_set(v_reuseFailAlloc_3636_, 1, v___x_3616_);
                    v___x_3618_ = v_reuseFailAlloc_3636_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3618_);
                v___x_3619_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3618_);
                v_second_3620_ = lean_ctor_get(v___x_3619_, 0);
                lean_inc(v_second_3620_);
                v_nano_3621_ = lean_ctor_get(v___x_3619_, 1);
                lean_inc(v_nano_3621_);
                lean_dec_ref(v___x_3619_);
                v___f_3622_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3622_, 0, v___x_3618_);
                v___x_3623_ = lean_int_neg(v_offset_3614_);
                v___x_3624_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3625_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3626_ = lean_int_mul(v_second_3620_, v___x_3625_);
                lean_dec(v_second_3620_);
                v___x_3627_ = lean_int_add(v___x_3626_, v_nano_3621_);
                lean_dec(v_nano_3621_);
                lean_dec(v___x_3626_);
                v___x_3628_ = lean_int_mul(v___x_3623_, v___x_3625_);
                lean_dec(v___x_3623_);
                v___x_3629_ = lean_int_add(v___x_3628_, v___x_3624_);
                lean_dec(v___x_3628_);
                v___x_3630_ = lean_int_add(v___x_3627_, v___x_3629_);
                lean_dec(v___x_3629_);
                lean_dec(v___x_3627_);
                v_tm_3631_ = l_Std_Time_Duration_ofNanoseconds(v___x_3630_);
                lean_dec(v___x_3630_);
                v___x_3632_ = lean_mk_thunk(v___f_3622_);
                if v_isShared_3601_ == 0 {
                    lean_ctor_set(v___x_3600_, 1, v___x_3632_);
                    lean_ctor_set(v___x_3600_, 0, v_tm_3631_);
                    v___x_3634_ = v___x_3600_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_tm_3631_);
                    lean_ctor_set(v_reuseFailAlloc_3635_, 1, v___x_3632_);
                    v___x_3634_ = v_reuseFailAlloc_3635_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3634_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withMinutes___boxed(
    mut v_tz_3643_: *mut LeanObject,
    mut v_dt_3644_: *mut LeanObject,
    mut v_minute_3645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3646_: *mut LeanObject = core::ptr::null_mut();
    v_res_3646_ = l_Std_Time_DateTime_withMinutes(v_tz_3643_, v_dt_3644_, v_minute_3645_);
    lean_dec_ref(v_tz_3643_);
    return v_res_3646_;
}
pub unsafe fn l_Std_Time_DateTime_withSeconds(
    mut v_tz_3647_: *mut LeanObject,
    mut v_dt_3648_: *mut LeanObject,
    mut v_second_3649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v_hour_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_offset_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_unused_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v_unused_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3650_ = lean_ctor_get(v_dt_3648_, 1);
                v_isSharedCheck_3693_ = (!lean_is_exclusive(v_dt_3648_)) as u8;
                if v_isSharedCheck_3693_ == 0 {
                    v_unused_3694_ = lean_ctor_get(v_dt_3648_, 0);
                    lean_dec(v_unused_3694_);
                    v___x_3652_ = v_dt_3648_;
                    v_isShared_3653_ = v_isSharedCheck_3693_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3650_);
                    lean_dec(v_dt_3648_);
                    v___x_3652_ = lean_box(0);
                    v_isShared_3653_ = v_isSharedCheck_3693_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3654_ = lean_thunk_get_own(v_date_3650_);
                lean_dec_ref(v_date_3650_);
                v_time_3655_ = lean_ctor_get(v___x_3654_, 1);
                v_date_3656_ = lean_ctor_get(v___x_3654_, 0);
                v_isSharedCheck_3692_ = (!lean_is_exclusive(v___x_3654_)) as u8;
                if v_isSharedCheck_3692_ == 0 {
                    v___x_3658_ = v___x_3654_;
                    v_isShared_3659_ = v_isSharedCheck_3692_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3655_);
                    lean_inc(v_date_3656_);
                    lean_dec(v___x_3654_);
                    v___x_3658_ = lean_box(0);
                    v_isShared_3659_ = v_isSharedCheck_3692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3660_ = lean_ctor_get(v_time_3655_, 0);
                v_minute_3661_ = lean_ctor_get(v_time_3655_, 1);
                v_nanosecond_3662_ = lean_ctor_get(v_time_3655_, 3);
                v_isSharedCheck_3690_ = (!lean_is_exclusive(v_time_3655_)) as u8;
                if v_isSharedCheck_3690_ == 0 {
                    v_unused_3691_ = lean_ctor_get(v_time_3655_, 2);
                    lean_dec(v_unused_3691_);
                    v___x_3664_ = v_time_3655_;
                    v_isShared_3665_ = v_isSharedCheck_3690_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_3662_);
                    lean_inc(v_minute_3661_);
                    lean_inc(v_hour_3660_);
                    lean_dec(v_time_3655_);
                    v___x_3664_ = lean_box(0);
                    v_isShared_3665_ = v_isSharedCheck_3690_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3666_ = lean_ctor_get(v_tz_3647_, 0);
                if v_isShared_3665_ == 0 {
                    lean_ctor_set(v___x_3664_, 2, v_second_3649_);
                    v___x_3668_ = v___x_3664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_hour_3660_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_minute_3661_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_second_3649_);
                    lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_nanosecond_3662_);
                    v___x_3668_ = v_reuseFailAlloc_3689_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3659_ == 0 {
                    lean_ctor_set(v___x_3658_, 1, v___x_3668_);
                    v___x_3670_ = v___x_3658_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_date_3656_);
                    lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3668_);
                    v___x_3670_ = v_reuseFailAlloc_3688_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3670_);
                v___x_3671_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3670_);
                v_second_3672_ = lean_ctor_get(v___x_3671_, 0);
                lean_inc(v_second_3672_);
                v_nano_3673_ = lean_ctor_get(v___x_3671_, 1);
                lean_inc(v_nano_3673_);
                lean_dec_ref(v___x_3671_);
                v___f_3674_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3674_, 0, v___x_3670_);
                v___x_3675_ = lean_int_neg(v_offset_3666_);
                v___x_3676_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3677_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3678_ = lean_int_mul(v_second_3672_, v___x_3677_);
                lean_dec(v_second_3672_);
                v___x_3679_ = lean_int_add(v___x_3678_, v_nano_3673_);
                lean_dec(v_nano_3673_);
                lean_dec(v___x_3678_);
                v___x_3680_ = lean_int_mul(v___x_3675_, v___x_3677_);
                lean_dec(v___x_3675_);
                v___x_3681_ = lean_int_add(v___x_3680_, v___x_3676_);
                lean_dec(v___x_3680_);
                v___x_3682_ = lean_int_add(v___x_3679_, v___x_3681_);
                lean_dec(v___x_3681_);
                lean_dec(v___x_3679_);
                v_tm_3683_ = l_Std_Time_Duration_ofNanoseconds(v___x_3682_);
                lean_dec(v___x_3682_);
                v___x_3684_ = lean_mk_thunk(v___f_3674_);
                if v_isShared_3653_ == 0 {
                    lean_ctor_set(v___x_3652_, 1, v___x_3684_);
                    lean_ctor_set(v___x_3652_, 0, v_tm_3683_);
                    v___x_3686_ = v___x_3652_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_tm_3683_);
                    lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3684_);
                    v___x_3686_ = v_reuseFailAlloc_3687_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withSeconds___boxed(
    mut v_tz_3695_: *mut LeanObject,
    mut v_dt_3696_: *mut LeanObject,
    mut v_second_3697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3698_: *mut LeanObject = core::ptr::null_mut();
    v_res_3698_ = l_Std_Time_DateTime_withSeconds(v_tz_3695_, v_dt_3696_, v_second_3697_);
    lean_dec_ref(v_tz_3695_);
    return v_res_3698_;
}
pub unsafe fn l_Std_Time_DateTime_withNanoseconds(
    mut v_tz_3699_: *mut LeanObject,
    mut v_dt_3700_: *mut LeanObject,
    mut v_nano_3701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v_hour_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3717_: u8 = 0;
    let mut v_offset_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v_unused_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3744_: u8 = 0;
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_unused_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3702_ = lean_ctor_get(v_dt_3700_, 1);
                v_isSharedCheck_3745_ = (!lean_is_exclusive(v_dt_3700_)) as u8;
                if v_isSharedCheck_3745_ == 0 {
                    v_unused_3746_ = lean_ctor_get(v_dt_3700_, 0);
                    lean_dec(v_unused_3746_);
                    v___x_3704_ = v_dt_3700_;
                    v_isShared_3705_ = v_isSharedCheck_3745_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3702_);
                    lean_dec(v_dt_3700_);
                    v___x_3704_ = lean_box(0);
                    v_isShared_3705_ = v_isSharedCheck_3745_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3706_ = lean_thunk_get_own(v_date_3702_);
                lean_dec_ref(v_date_3702_);
                v_time_3707_ = lean_ctor_get(v___x_3706_, 1);
                v_date_3708_ = lean_ctor_get(v___x_3706_, 0);
                v_isSharedCheck_3744_ = (!lean_is_exclusive(v___x_3706_)) as u8;
                if v_isSharedCheck_3744_ == 0 {
                    v___x_3710_ = v___x_3706_;
                    v_isShared_3711_ = v_isSharedCheck_3744_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3707_);
                    lean_inc(v_date_3708_);
                    lean_dec(v___x_3706_);
                    v___x_3710_ = lean_box(0);
                    v_isShared_3711_ = v_isSharedCheck_3744_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3712_ = lean_ctor_get(v_time_3707_, 0);
                v_minute_3713_ = lean_ctor_get(v_time_3707_, 1);
                v_second_3714_ = lean_ctor_get(v_time_3707_, 2);
                v_isSharedCheck_3742_ = (!lean_is_exclusive(v_time_3707_)) as u8;
                if v_isSharedCheck_3742_ == 0 {
                    v_unused_3743_ = lean_ctor_get(v_time_3707_, 3);
                    lean_dec(v_unused_3743_);
                    v___x_3716_ = v_time_3707_;
                    v_isShared_3717_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_second_3714_);
                    lean_inc(v_minute_3713_);
                    lean_inc(v_hour_3712_);
                    lean_dec(v_time_3707_);
                    v___x_3716_ = lean_box(0);
                    v_isShared_3717_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3718_ = lean_ctor_get(v_tz_3699_, 0);
                if v_isShared_3717_ == 0 {
                    lean_ctor_set(v___x_3716_, 3, v_nano_3701_);
                    v___x_3720_ = v___x_3716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_hour_3712_);
                    lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_minute_3713_);
                    lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_second_3714_);
                    lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_nano_3701_);
                    v___x_3720_ = v_reuseFailAlloc_3741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3711_ == 0 {
                    lean_ctor_set(v___x_3710_, 1, v___x_3720_);
                    v___x_3722_ = v___x_3710_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3740_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_date_3708_);
                    lean_ctor_set(v_reuseFailAlloc_3740_, 1, v___x_3720_);
                    v___x_3722_ = v_reuseFailAlloc_3740_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3722_);
                v___x_3723_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3722_);
                v_second_3724_ = lean_ctor_get(v___x_3723_, 0);
                lean_inc(v_second_3724_);
                v_nano_3725_ = lean_ctor_get(v___x_3723_, 1);
                lean_inc(v_nano_3725_);
                lean_dec_ref(v___x_3723_);
                v___f_3726_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3726_, 0, v___x_3722_);
                v___x_3727_ = lean_int_neg(v_offset_3718_);
                v___x_3728_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3729_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3730_ = lean_int_mul(v_second_3724_, v___x_3729_);
                lean_dec(v_second_3724_);
                v___x_3731_ = lean_int_add(v___x_3730_, v_nano_3725_);
                lean_dec(v_nano_3725_);
                lean_dec(v___x_3730_);
                v___x_3732_ = lean_int_mul(v___x_3727_, v___x_3729_);
                lean_dec(v___x_3727_);
                v___x_3733_ = lean_int_add(v___x_3732_, v___x_3728_);
                lean_dec(v___x_3732_);
                v___x_3734_ = lean_int_add(v___x_3731_, v___x_3733_);
                lean_dec(v___x_3733_);
                lean_dec(v___x_3731_);
                v_tm_3735_ = l_Std_Time_Duration_ofNanoseconds(v___x_3734_);
                lean_dec(v___x_3734_);
                v___x_3736_ = lean_mk_thunk(v___f_3726_);
                if v_isShared_3705_ == 0 {
                    lean_ctor_set(v___x_3704_, 1, v___x_3736_);
                    lean_ctor_set(v___x_3704_, 0, v_tm_3735_);
                    v___x_3738_ = v___x_3704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_tm_3735_);
                    lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3736_);
                    v___x_3738_ = v_reuseFailAlloc_3739_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withNanoseconds___boxed(
    mut v_tz_3747_: *mut LeanObject,
    mut v_dt_3748_: *mut LeanObject,
    mut v_nano_3749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3750_: *mut LeanObject = core::ptr::null_mut();
    v_res_3750_ = l_Std_Time_DateTime_withNanoseconds(v_tz_3747_, v_dt_3748_, v_nano_3749_);
    lean_dec_ref(v_tz_3747_);
    return v_res_3750_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withMilliseconds___closed__0() -> *mut LeanObject {
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    v___x_3751_ = lean_unsigned_to_nat(1000);
    v___x_3752_ = lean_nat_to_int(v___x_3751_);
    return v___x_3752_;
}
pub unsafe fn l_Std_Time_DateTime_withMilliseconds(
    mut v_tz_3753_: *mut LeanObject,
    mut v_dt_3754_: *mut LeanObject,
    mut v_milli_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3759_: u8 = 0;
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v_hour_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v_offset_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_isSharedCheck_3804_: u8 = 0;
    let mut v_unused_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3756_ = lean_ctor_get(v_dt_3754_, 1);
                v_isSharedCheck_3804_ = (!lean_is_exclusive(v_dt_3754_)) as u8;
                if v_isSharedCheck_3804_ == 0 {
                    v_unused_3805_ = lean_ctor_get(v_dt_3754_, 0);
                    lean_dec(v_unused_3805_);
                    v___x_3758_ = v_dt_3754_;
                    v_isShared_3759_ = v_isSharedCheck_3804_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3756_);
                    lean_dec(v_dt_3754_);
                    v___x_3758_ = lean_box(0);
                    v_isShared_3759_ = v_isSharedCheck_3804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3760_ = lean_thunk_get_own(v_date_3756_);
                lean_dec_ref(v_date_3756_);
                v_time_3761_ = lean_ctor_get(v___x_3760_, 1);
                v_date_3762_ = lean_ctor_get(v___x_3760_, 0);
                v_isSharedCheck_3803_ = (!lean_is_exclusive(v___x_3760_)) as u8;
                if v_isSharedCheck_3803_ == 0 {
                    v___x_3764_ = v___x_3760_;
                    v_isShared_3765_ = v_isSharedCheck_3803_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_time_3761_);
                    lean_inc(v_date_3762_);
                    lean_dec(v___x_3760_);
                    v___x_3764_ = lean_box(0);
                    v_isShared_3765_ = v_isSharedCheck_3803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3766_ = lean_ctor_get(v_time_3761_, 0);
                v_minute_3767_ = lean_ctor_get(v_time_3761_, 1);
                v_second_3768_ = lean_ctor_get(v_time_3761_, 2);
                v_nanosecond_3769_ = lean_ctor_get(v_time_3761_, 3);
                v_isSharedCheck_3802_ = (!lean_is_exclusive(v_time_3761_)) as u8;
                if v_isSharedCheck_3802_ == 0 {
                    v___x_3771_ = v_time_3761_;
                    v_isShared_3772_ = v_isSharedCheck_3802_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_nanosecond_3769_);
                    lean_inc(v_second_3768_);
                    lean_inc(v_minute_3767_);
                    lean_inc(v_hour_3766_);
                    lean_dec(v_time_3761_);
                    v___x_3771_ = lean_box(0);
                    v_isShared_3772_ = v_isSharedCheck_3802_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3773_ = lean_ctor_get(v_tz_3753_, 0);
                v___x_3774_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_withMilliseconds___closed__0,
                );
                v___x_3775_ = lean_int_emod(v_nanosecond_3769_, v___x_3774_);
                lean_dec(v_nanosecond_3769_);
                v___x_3776_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_addMilliseconds___closed__0,
                );
                v___x_3777_ = lean_int_mul(v_milli_3755_, v___x_3776_);
                v___x_3778_ = lean_int_add(v___x_3777_, v___x_3775_);
                lean_dec(v___x_3775_);
                lean_dec(v___x_3777_);
                if v_isShared_3772_ == 0 {
                    lean_ctor_set(v___x_3771_, 3, v___x_3778_);
                    v___x_3780_ = v___x_3771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3801_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_hour_3766_);
                    lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_minute_3767_);
                    lean_ctor_set(v_reuseFailAlloc_3801_, 2, v_second_3768_);
                    lean_ctor_set(v_reuseFailAlloc_3801_, 3, v___x_3778_);
                    v___x_3780_ = v_reuseFailAlloc_3801_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3765_ == 0 {
                    lean_ctor_set(v___x_3764_, 1, v___x_3780_);
                    v___x_3782_ = v___x_3764_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_date_3762_);
                    lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3780_);
                    v___x_3782_ = v_reuseFailAlloc_3800_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref(v___x_3782_);
                v___x_3783_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3782_);
                v_second_3784_ = lean_ctor_get(v___x_3783_, 0);
                lean_inc(v_second_3784_);
                v_nano_3785_ = lean_ctor_get(v___x_3783_, 1);
                lean_inc(v_nano_3785_);
                lean_dec_ref(v___x_3783_);
                v___f_3786_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_3786_, 0, v___x_3782_);
                v___x_3787_ = lean_int_neg(v_offset_3773_);
                v___x_3788_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3789_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3790_ = lean_int_mul(v_second_3784_, v___x_3789_);
                lean_dec(v_second_3784_);
                v___x_3791_ = lean_int_add(v___x_3790_, v_nano_3785_);
                lean_dec(v_nano_3785_);
                lean_dec(v___x_3790_);
                v___x_3792_ = lean_int_mul(v___x_3787_, v___x_3789_);
                lean_dec(v___x_3787_);
                v___x_3793_ = lean_int_add(v___x_3792_, v___x_3788_);
                lean_dec(v___x_3792_);
                v___x_3794_ = lean_int_add(v___x_3791_, v___x_3793_);
                lean_dec(v___x_3793_);
                lean_dec(v___x_3791_);
                v_tm_3795_ = l_Std_Time_Duration_ofNanoseconds(v___x_3794_);
                lean_dec(v___x_3794_);
                v___x_3796_ = lean_mk_thunk(v___f_3786_);
                if v_isShared_3759_ == 0 {
                    lean_ctor_set(v___x_3758_, 1, v___x_3796_);
                    lean_ctor_set(v___x_3758_, 0, v_tm_3795_);
                    v___x_3798_ = v___x_3758_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_tm_3795_);
                    lean_ctor_set(v_reuseFailAlloc_3799_, 1, v___x_3796_);
                    v___x_3798_ = v_reuseFailAlloc_3799_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withMilliseconds___boxed(
    mut v_tz_3806_: *mut LeanObject,
    mut v_dt_3807_: *mut LeanObject,
    mut v_milli_3808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3809_: *mut LeanObject = core::ptr::null_mut();
    v_res_3809_ = l_Std_Time_DateTime_withMilliseconds(v_tz_3806_, v_dt_3807_, v_milli_3808_);
    lean_dec(v_milli_3808_);
    lean_dec_ref(v_tz_3806_);
    return v_res_3809_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime___redArg(
    mut v_dt_3810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    v_date_3811_ = lean_ctor_get(v_dt_3810_, 1);
    v___x_3812_ = lean_thunk_get_own(v_date_3811_);
    return v___x_3812_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(
    mut v_dt_3813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3814_: *mut LeanObject = core::ptr::null_mut();
    v_res_3814_ = l_Std_Time_DateTime_toPlainDateTime___redArg(v_dt_3813_);
    lean_dec_ref(v_dt_3813_);
    return v_res_3814_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime(
    mut v_tz_3815_: *mut LeanObject,
    mut v_dt_3816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    v_date_3817_ = lean_ctor_get(v_dt_3816_, 1);
    v___x_3818_ = lean_thunk_get_own(v_date_3817_);
    return v___x_3818_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime___boxed(
    mut v_tz_3819_: *mut LeanObject,
    mut v_dt_3820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3821_: *mut LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Std_Time_DateTime_toPlainDateTime(v_tz_3819_, v_dt_3820_);
    lean_dec_ref(v_dt_3820_);
    lean_dec_ref(v_tz_3819_);
    return v_res_3821_;
}
pub unsafe fn l_Std_Time_DateTime_year___redArg(
    mut v_dt_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3826_: *mut LeanObject = core::ptr::null_mut();
    v_date_3823_ = lean_ctor_get(v_dt_3822_, 1);
    v___x_3824_ = lean_thunk_get_own(v_date_3823_);
    v_date_3825_ = lean_ctor_get(v___x_3824_, 0);
    lean_inc_ref(v_date_3825_);
    lean_dec(v___x_3824_);
    v_year_3826_ = lean_ctor_get(v_date_3825_, 0);
    lean_inc(v_year_3826_);
    lean_dec_ref(v_date_3825_);
    return v_year_3826_;
}
pub unsafe fn l_Std_Time_DateTime_year___redArg___boxed(
    mut v_dt_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3828_: *mut LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_Std_Time_DateTime_year___redArg(v_dt_3827_);
    lean_dec_ref(v_dt_3827_);
    return v_res_3828_;
}
pub unsafe fn l_Std_Time_DateTime_year(
    mut v_tz_3829_: *mut LeanObject,
    mut v_dt_3830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3834_: *mut LeanObject = core::ptr::null_mut();
    v_date_3831_ = lean_ctor_get(v_dt_3830_, 1);
    v___x_3832_ = lean_thunk_get_own(v_date_3831_);
    v_date_3833_ = lean_ctor_get(v___x_3832_, 0);
    lean_inc_ref(v_date_3833_);
    lean_dec(v___x_3832_);
    v_year_3834_ = lean_ctor_get(v_date_3833_, 0);
    lean_inc(v_year_3834_);
    lean_dec_ref(v_date_3833_);
    return v_year_3834_;
}
pub unsafe fn l_Std_Time_DateTime_year___boxed(
    mut v_tz_3835_: *mut LeanObject,
    mut v_dt_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3837_: *mut LeanObject = core::ptr::null_mut();
    v_res_3837_ = l_Std_Time_DateTime_year(v_tz_3835_, v_dt_3836_);
    lean_dec_ref(v_dt_3836_);
    lean_dec_ref(v_tz_3835_);
    return v_res_3837_;
}
pub unsafe fn l_Std_Time_DateTime_month___redArg(
    mut v_dt_3838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3842_: *mut LeanObject = core::ptr::null_mut();
    v_date_3839_ = lean_ctor_get(v_dt_3838_, 1);
    v___x_3840_ = lean_thunk_get_own(v_date_3839_);
    v_date_3841_ = lean_ctor_get(v___x_3840_, 0);
    lean_inc_ref(v_date_3841_);
    lean_dec(v___x_3840_);
    v_month_3842_ = lean_ctor_get(v_date_3841_, 1);
    lean_inc(v_month_3842_);
    lean_dec_ref(v_date_3841_);
    return v_month_3842_;
}
pub unsafe fn l_Std_Time_DateTime_month___redArg___boxed(
    mut v_dt_3843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3844_: *mut LeanObject = core::ptr::null_mut();
    v_res_3844_ = l_Std_Time_DateTime_month___redArg(v_dt_3843_);
    lean_dec_ref(v_dt_3843_);
    return v_res_3844_;
}
pub unsafe fn l_Std_Time_DateTime_month(
    mut v_tz_3845_: *mut LeanObject,
    mut v_dt_3846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_month_3850_: *mut LeanObject = core::ptr::null_mut();
    v_date_3847_ = lean_ctor_get(v_dt_3846_, 1);
    v___x_3848_ = lean_thunk_get_own(v_date_3847_);
    v_date_3849_ = lean_ctor_get(v___x_3848_, 0);
    lean_inc_ref(v_date_3849_);
    lean_dec(v___x_3848_);
    v_month_3850_ = lean_ctor_get(v_date_3849_, 1);
    lean_inc(v_month_3850_);
    lean_dec_ref(v_date_3849_);
    return v_month_3850_;
}
pub unsafe fn l_Std_Time_DateTime_month___boxed(
    mut v_tz_3851_: *mut LeanObject,
    mut v_dt_3852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3853_: *mut LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Std_Time_DateTime_month(v_tz_3851_, v_dt_3852_);
    lean_dec_ref(v_dt_3852_);
    lean_dec_ref(v_tz_3851_);
    return v_res_3853_;
}
pub unsafe fn l_Std_Time_DateTime_day___redArg(mut v_dt_3854_: *mut LeanObject) -> *mut LeanObject {
    let mut v_date_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3858_: *mut LeanObject = core::ptr::null_mut();
    v_date_3855_ = lean_ctor_get(v_dt_3854_, 1);
    v___x_3856_ = lean_thunk_get_own(v_date_3855_);
    v_date_3857_ = lean_ctor_get(v___x_3856_, 0);
    lean_inc_ref(v_date_3857_);
    lean_dec(v___x_3856_);
    v_day_3858_ = lean_ctor_get(v_date_3857_, 2);
    lean_inc(v_day_3858_);
    lean_dec_ref(v_date_3857_);
    return v_day_3858_;
}
pub unsafe fn l_Std_Time_DateTime_day___redArg___boxed(
    mut v_dt_3859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3860_: *mut LeanObject = core::ptr::null_mut();
    v_res_3860_ = l_Std_Time_DateTime_day___redArg(v_dt_3859_);
    lean_dec_ref(v_dt_3859_);
    return v_res_3860_;
}
pub unsafe fn l_Std_Time_DateTime_day(
    mut v_tz_3861_: *mut LeanObject,
    mut v_dt_3862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_3866_: *mut LeanObject = core::ptr::null_mut();
    v_date_3863_ = lean_ctor_get(v_dt_3862_, 1);
    v___x_3864_ = lean_thunk_get_own(v_date_3863_);
    v_date_3865_ = lean_ctor_get(v___x_3864_, 0);
    lean_inc_ref(v_date_3865_);
    lean_dec(v___x_3864_);
    v_day_3866_ = lean_ctor_get(v_date_3865_, 2);
    lean_inc(v_day_3866_);
    lean_dec_ref(v_date_3865_);
    return v_day_3866_;
}
pub unsafe fn l_Std_Time_DateTime_day___boxed(
    mut v_tz_3867_: *mut LeanObject,
    mut v_dt_3868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3869_: *mut LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Std_Time_DateTime_day(v_tz_3867_, v_dt_3868_);
    lean_dec_ref(v_dt_3868_);
    lean_dec_ref(v_tz_3867_);
    return v_res_3869_;
}
pub unsafe fn l_Std_Time_DateTime_hour___redArg(
    mut v_dt_3870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hour_3874_: *mut LeanObject = core::ptr::null_mut();
    v_date_3871_ = lean_ctor_get(v_dt_3870_, 1);
    v___x_3872_ = lean_thunk_get_own(v_date_3871_);
    v_time_3873_ = lean_ctor_get(v___x_3872_, 1);
    lean_inc_ref(v_time_3873_);
    lean_dec(v___x_3872_);
    v_hour_3874_ = lean_ctor_get(v_time_3873_, 0);
    lean_inc(v_hour_3874_);
    lean_dec_ref(v_time_3873_);
    return v_hour_3874_;
}
pub unsafe fn l_Std_Time_DateTime_hour___redArg___boxed(
    mut v_dt_3875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3876_: *mut LeanObject = core::ptr::null_mut();
    v_res_3876_ = l_Std_Time_DateTime_hour___redArg(v_dt_3875_);
    lean_dec_ref(v_dt_3875_);
    return v_res_3876_;
}
pub unsafe fn l_Std_Time_DateTime_hour(
    mut v_tz_3877_: *mut LeanObject,
    mut v_dt_3878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hour_3882_: *mut LeanObject = core::ptr::null_mut();
    v_date_3879_ = lean_ctor_get(v_dt_3878_, 1);
    v___x_3880_ = lean_thunk_get_own(v_date_3879_);
    v_time_3881_ = lean_ctor_get(v___x_3880_, 1);
    lean_inc_ref(v_time_3881_);
    lean_dec(v___x_3880_);
    v_hour_3882_ = lean_ctor_get(v_time_3881_, 0);
    lean_inc(v_hour_3882_);
    lean_dec_ref(v_time_3881_);
    return v_hour_3882_;
}
pub unsafe fn l_Std_Time_DateTime_hour___boxed(
    mut v_tz_3883_: *mut LeanObject,
    mut v_dt_3884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3885_: *mut LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Std_Time_DateTime_hour(v_tz_3883_, v_dt_3884_);
    lean_dec_ref(v_dt_3884_);
    lean_dec_ref(v_tz_3883_);
    return v_res_3885_;
}
pub unsafe fn l_Std_Time_DateTime_minute___redArg(
    mut v_dt_3886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_3890_: *mut LeanObject = core::ptr::null_mut();
    v_date_3887_ = lean_ctor_get(v_dt_3886_, 1);
    v___x_3888_ = lean_thunk_get_own(v_date_3887_);
    v_time_3889_ = lean_ctor_get(v___x_3888_, 1);
    lean_inc_ref(v_time_3889_);
    lean_dec(v___x_3888_);
    v_minute_3890_ = lean_ctor_get(v_time_3889_, 1);
    lean_inc(v_minute_3890_);
    lean_dec_ref(v_time_3889_);
    return v_minute_3890_;
}
pub unsafe fn l_Std_Time_DateTime_minute___redArg___boxed(
    mut v_dt_3891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3892_: *mut LeanObject = core::ptr::null_mut();
    v_res_3892_ = l_Std_Time_DateTime_minute___redArg(v_dt_3891_);
    lean_dec_ref(v_dt_3891_);
    return v_res_3892_;
}
pub unsafe fn l_Std_Time_DateTime_minute(
    mut v_tz_3893_: *mut LeanObject,
    mut v_dt_3894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_3898_: *mut LeanObject = core::ptr::null_mut();
    v_date_3895_ = lean_ctor_get(v_dt_3894_, 1);
    v___x_3896_ = lean_thunk_get_own(v_date_3895_);
    v_time_3897_ = lean_ctor_get(v___x_3896_, 1);
    lean_inc_ref(v_time_3897_);
    lean_dec(v___x_3896_);
    v_minute_3898_ = lean_ctor_get(v_time_3897_, 1);
    lean_inc(v_minute_3898_);
    lean_dec_ref(v_time_3897_);
    return v_minute_3898_;
}
pub unsafe fn l_Std_Time_DateTime_minute___boxed(
    mut v_tz_3899_: *mut LeanObject,
    mut v_dt_3900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3901_: *mut LeanObject = core::ptr::null_mut();
    v_res_3901_ = l_Std_Time_DateTime_minute(v_tz_3899_, v_dt_3900_);
    lean_dec_ref(v_dt_3900_);
    lean_dec_ref(v_tz_3899_);
    return v_res_3901_;
}
pub unsafe fn l_Std_Time_DateTime_second___redArg(
    mut v_dt_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3906_: *mut LeanObject = core::ptr::null_mut();
    v_date_3903_ = lean_ctor_get(v_dt_3902_, 1);
    v___x_3904_ = lean_thunk_get_own(v_date_3903_);
    v_time_3905_ = lean_ctor_get(v___x_3904_, 1);
    lean_inc_ref(v_time_3905_);
    lean_dec(v___x_3904_);
    v_second_3906_ = lean_ctor_get(v_time_3905_, 2);
    lean_inc(v_second_3906_);
    lean_dec_ref(v_time_3905_);
    return v_second_3906_;
}
pub unsafe fn l_Std_Time_DateTime_second___redArg___boxed(
    mut v_dt_3907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3908_: *mut LeanObject = core::ptr::null_mut();
    v_res_3908_ = l_Std_Time_DateTime_second___redArg(v_dt_3907_);
    lean_dec_ref(v_dt_3907_);
    return v_res_3908_;
}
pub unsafe fn l_Std_Time_DateTime_second(
    mut v_tz_3909_: *mut LeanObject,
    mut v_dt_3910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3914_: *mut LeanObject = core::ptr::null_mut();
    v_date_3911_ = lean_ctor_get(v_dt_3910_, 1);
    v___x_3912_ = lean_thunk_get_own(v_date_3911_);
    v_time_3913_ = lean_ctor_get(v___x_3912_, 1);
    lean_inc_ref(v_time_3913_);
    lean_dec(v___x_3912_);
    v_second_3914_ = lean_ctor_get(v_time_3913_, 2);
    lean_inc(v_second_3914_);
    lean_dec_ref(v_time_3913_);
    return v_second_3914_;
}
pub unsafe fn l_Std_Time_DateTime_second___boxed(
    mut v_tz_3915_: *mut LeanObject,
    mut v_dt_3916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3917_: *mut LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Std_Time_DateTime_second(v_tz_3915_, v_dt_3916_);
    lean_dec_ref(v_dt_3916_);
    lean_dec_ref(v_tz_3915_);
    return v_res_3917_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond___redArg(
    mut v_dt_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    v_date_3919_ = lean_ctor_get(v_dt_3918_, 1);
    v___x_3920_ = lean_thunk_get_own(v_date_3919_);
    v_time_3921_ = lean_ctor_get(v___x_3920_, 1);
    lean_inc_ref(v_time_3921_);
    lean_dec(v___x_3920_);
    v_nanosecond_3922_ = lean_ctor_get(v_time_3921_, 3);
    lean_inc(v_nanosecond_3922_);
    lean_dec_ref(v_time_3921_);
    v___x_3923_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0_once),
        _init_l_Std_Time_DateTime_withMilliseconds___closed__0,
    );
    v___x_3924_ = lean_int_emod(v_nanosecond_3922_, v___x_3923_);
    lean_dec(v_nanosecond_3922_);
    return v___x_3924_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond___redArg___boxed(
    mut v_dt_3925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3926_: *mut LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Std_Time_DateTime_millisecond___redArg(v_dt_3925_);
    lean_dec_ref(v_dt_3925_);
    return v_res_3926_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond(
    mut v_tz_3927_: *mut LeanObject,
    mut v_dt_3928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    v_date_3929_ = lean_ctor_get(v_dt_3928_, 1);
    v___x_3930_ = lean_thunk_get_own(v_date_3929_);
    v_time_3931_ = lean_ctor_get(v___x_3930_, 1);
    lean_inc_ref(v_time_3931_);
    lean_dec(v___x_3930_);
    v_nanosecond_3932_ = lean_ctor_get(v_time_3931_, 3);
    lean_inc(v_nanosecond_3932_);
    lean_dec_ref(v_time_3931_);
    v___x_3933_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0_once),
        _init_l_Std_Time_DateTime_withMilliseconds___closed__0,
    );
    v___x_3934_ = lean_int_emod(v_nanosecond_3932_, v___x_3933_);
    lean_dec(v_nanosecond_3932_);
    return v___x_3934_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond___boxed(
    mut v_tz_3935_: *mut LeanObject,
    mut v_dt_3936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3937_: *mut LeanObject = core::ptr::null_mut();
    v_res_3937_ = l_Std_Time_DateTime_millisecond(v_tz_3935_, v_dt_3936_);
    lean_dec_ref(v_dt_3936_);
    lean_dec_ref(v_tz_3935_);
    return v_res_3937_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond___redArg(
    mut v_dt_3938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3942_: *mut LeanObject = core::ptr::null_mut();
    v_date_3939_ = lean_ctor_get(v_dt_3938_, 1);
    v___x_3940_ = lean_thunk_get_own(v_date_3939_);
    v_time_3941_ = lean_ctor_get(v___x_3940_, 1);
    lean_inc_ref(v_time_3941_);
    lean_dec(v___x_3940_);
    v_nanosecond_3942_ = lean_ctor_get(v_time_3941_, 3);
    lean_inc(v_nanosecond_3942_);
    lean_dec_ref(v_time_3941_);
    return v_nanosecond_3942_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond___redArg___boxed(
    mut v_dt_3943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3944_: *mut LeanObject = core::ptr::null_mut();
    v_res_3944_ = l_Std_Time_DateTime_nanosecond___redArg(v_dt_3943_);
    lean_dec_ref(v_dt_3943_);
    return v_res_3944_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond(
    mut v_tz_3945_: *mut LeanObject,
    mut v_dt_3946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3950_: *mut LeanObject = core::ptr::null_mut();
    v_date_3947_ = lean_ctor_get(v_dt_3946_, 1);
    v___x_3948_ = lean_thunk_get_own(v_date_3947_);
    v_time_3949_ = lean_ctor_get(v___x_3948_, 1);
    lean_inc_ref(v_time_3949_);
    lean_dec(v___x_3948_);
    v_nanosecond_3950_ = lean_ctor_get(v_time_3949_, 3);
    lean_inc(v_nanosecond_3950_);
    lean_dec_ref(v_time_3949_);
    return v_nanosecond_3950_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond___boxed(
    mut v_tz_3951_: *mut LeanObject,
    mut v_dt_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3953_: *mut LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Std_Time_DateTime_nanosecond(v_tz_3951_, v_dt_3952_);
    lean_dec_ref(v_dt_3952_);
    lean_dec_ref(v_tz_3951_);
    return v_res_3953_;
}
pub unsafe fn l_Std_Time_DateTime_weekday___redArg(mut v_dt_3954_: *mut LeanObject) -> u8 {
    let mut v_date_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    v_date_3955_ = lean_ctor_get(v_dt_3954_, 1);
    v___x_3956_ = lean_thunk_get_own(v_date_3955_);
    v_date_3957_ = lean_ctor_get(v___x_3956_, 0);
    lean_inc_ref(v_date_3957_);
    lean_dec(v___x_3956_);
    v___x_3958_ = l_Std_Time_PlainDate_weekday(v_date_3957_);
    return v___x_3958_;
}
pub unsafe fn l_Std_Time_DateTime_weekday___redArg___boxed(
    mut v_dt_3959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3960_: u8 = 0;
    let mut v_r_3961_: *mut LeanObject = core::ptr::null_mut();
    v_res_3960_ = l_Std_Time_DateTime_weekday___redArg(v_dt_3959_);
    lean_dec_ref(v_dt_3959_);
    v_r_3961_ = lean_box((v_res_3960_) as usize);
    return v_r_3961_;
}
pub unsafe fn l_Std_Time_DateTime_weekday(
    mut v_tz_3962_: *mut LeanObject,
    mut v_dt_3963_: *mut LeanObject,
) -> u8 {
    let mut v_date_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    v_date_3964_ = lean_ctor_get(v_dt_3963_, 1);
    v___x_3965_ = lean_thunk_get_own(v_date_3964_);
    v_date_3966_ = lean_ctor_get(v___x_3965_, 0);
    lean_inc_ref(v_date_3966_);
    lean_dec(v___x_3965_);
    v___x_3967_ = l_Std_Time_PlainDate_weekday(v_date_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Std_Time_DateTime_weekday___boxed(
    mut v_tz_3968_: *mut LeanObject,
    mut v_dt_3969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3970_: u8 = 0;
    let mut v_r_3971_: *mut LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_Std_Time_DateTime_weekday(v_tz_3968_, v_dt_3969_);
    lean_dec_ref(v_dt_3969_);
    lean_dec_ref(v_tz_3968_);
    v_r_3971_ = lean_box((v_res_3970_) as usize);
    return v_r_3971_;
}
pub unsafe fn l_Std_Time_DateTime_era___redArg(mut v_date_3972_: *mut LeanObject) -> u8 {
    let mut v_date_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    v_date_3973_ = lean_ctor_get(v_date_3972_, 1);
    v___x_3974_ = lean_thunk_get_own(v_date_3973_);
    v_date_3975_ = lean_ctor_get(v___x_3974_, 0);
    lean_inc_ref(v_date_3975_);
    lean_dec(v___x_3974_);
    v_year_3976_ = lean_ctor_get(v_date_3975_, 0);
    lean_inc(v_year_3976_);
    lean_dec_ref(v_date_3975_);
    v___x_3977_ = l_Std_Time_Year_Offset_era(v_year_3976_);
    lean_dec(v_year_3976_);
    return v___x_3977_;
}
pub unsafe fn l_Std_Time_DateTime_era___redArg___boxed(
    mut v_date_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3979_: u8 = 0;
    let mut v_r_3980_: *mut LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Std_Time_DateTime_era___redArg(v_date_3978_);
    lean_dec_ref(v_date_3978_);
    v_r_3980_ = lean_box((v_res_3979_) as usize);
    return v_r_3980_;
}
pub unsafe fn l_Std_Time_DateTime_era(
    mut v_tz_3981_: *mut LeanObject,
    mut v_date_3982_: *mut LeanObject,
) -> u8 {
    let mut v___x_3983_: u8 = 0;
    v___x_3983_ = l_Std_Time_DateTime_era___redArg(v_date_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Std_Time_DateTime_era___boxed(
    mut v_tz_3984_: *mut LeanObject,
    mut v_date_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3986_: u8 = 0;
    let mut v_r_3987_: *mut LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_Std_Time_DateTime_era(v_tz_3984_, v_date_3985_);
    lean_dec_ref(v_date_3985_);
    lean_dec_ref(v_tz_3984_);
    v_r_3987_ = lean_box((v_res_3986_) as usize);
    return v_r_3987_;
}
pub unsafe fn l_Std_Time_DateTime_withWeekday(
    mut v_tz_3988_: *mut LeanObject,
    mut v_dt_3989_: *mut LeanObject,
    mut v_desiredWeekday_3990_: u8,
) -> *mut LeanObject {
    let mut v_date_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3994_: u8 = 0;
    let mut v_offset_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4015_: u8 = 0;
    let mut v_unused_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3991_ = lean_ctor_get(v_dt_3989_, 1);
                v_isSharedCheck_4015_ = (!lean_is_exclusive(v_dt_3989_)) as u8;
                if v_isSharedCheck_4015_ == 0 {
                    v_unused_4016_ = lean_ctor_get(v_dt_3989_, 0);
                    lean_dec(v_unused_4016_);
                    v___x_3993_ = v_dt_3989_;
                    v_isShared_3994_ = v_isSharedCheck_4015_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_date_3991_);
                    lean_dec(v_dt_3989_);
                    v___x_3993_ = lean_box(0);
                    v_isShared_3994_ = v_isSharedCheck_4015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_offset_3995_ = lean_ctor_get(v_tz_3988_, 0);
                v___x_3996_ = lean_thunk_get_own(v_date_3991_);
                lean_dec_ref(v_date_3991_);
                v___x_3997_ =
                    l_Std_Time_PlainDateTime_withWeekday(v___x_3996_, v_desiredWeekday_3990_);
                lean_inc_ref(v___x_3997_);
                v___x_3998_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3997_);
                v_second_3999_ = lean_ctor_get(v___x_3998_, 0);
                lean_inc(v_second_3999_);
                v_nano_4000_ = lean_ctor_get(v___x_3998_, 1);
                lean_inc(v_nano_4000_);
                lean_dec_ref(v___x_3998_);
                v___f_4001_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4001_, 0, v___x_3997_);
                v___x_4002_ = lean_int_neg(v_offset_3995_);
                v___x_4003_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_4004_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4005_ = lean_int_mul(v_second_3999_, v___x_4004_);
                lean_dec(v_second_3999_);
                v___x_4006_ = lean_int_add(v___x_4005_, v_nano_4000_);
                lean_dec(v_nano_4000_);
                lean_dec(v___x_4005_);
                v___x_4007_ = lean_int_mul(v___x_4002_, v___x_4004_);
                lean_dec(v___x_4002_);
                v___x_4008_ = lean_int_add(v___x_4007_, v___x_4003_);
                lean_dec(v___x_4007_);
                v___x_4009_ = lean_int_add(v___x_4006_, v___x_4008_);
                lean_dec(v___x_4008_);
                lean_dec(v___x_4006_);
                v_tm_4010_ = l_Std_Time_Duration_ofNanoseconds(v___x_4009_);
                lean_dec(v___x_4009_);
                v___x_4011_ = lean_mk_thunk(v___f_4001_);
                if v_isShared_3994_ == 0 {
                    lean_ctor_set(v___x_3993_, 1, v___x_4011_);
                    lean_ctor_set(v___x_3993_, 0, v_tm_4010_);
                    v___x_4013_ = v___x_3993_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_tm_4010_);
                    lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4011_);
                    v___x_4013_ = v_reuseFailAlloc_4014_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withWeekday___boxed(
    mut v_tz_4017_: *mut LeanObject,
    mut v_dt_4018_: *mut LeanObject,
    mut v_desiredWeekday_4019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_desiredWeekday_boxed_4020_: u8 = 0;
    let mut v_res_4021_: *mut LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_4020_ = (lean_unbox(v_desiredWeekday_4019_) as u8);
    v_res_4021_ =
        l_Std_Time_DateTime_withWeekday(v_tz_4017_, v_dt_4018_, v_desiredWeekday_boxed_4020_);
    lean_dec_ref(v_tz_4017_);
    return v_res_4021_;
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear___redArg(mut v_date_4022_: *mut LeanObject) -> u8 {
    let mut v_date_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4023_ = lean_ctor_get(v_date_4022_, 1);
                v___x_4024_ = lean_thunk_get_own(v_date_4023_);
                v_date_4025_ = lean_ctor_get(v___x_4024_, 0);
                lean_inc_ref(v_date_4025_);
                lean_dec(v___x_4024_);
                v_year_4026_ = lean_ctor_get(v_date_4025_, 0);
                lean_inc(v_year_4026_);
                lean_dec_ref(v_date_4025_);
                v___x_4027_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_4028_ = lean_int_mod(v_year_4026_, v___x_4027_);
                v___x_4029_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_4034_ = lean_int_dec_eq(v___x_4028_, v___x_4029_);
                lean_dec(v___x_4028_);
                if v___x_4034_ == 0 {
                    lean_dec(v_year_4026_);
                    return v___x_4034_;
                } else {
                    v___x_4035_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_4036_ = lean_int_mod(v_year_4026_, v___x_4035_);
                    v___x_4037_ = lean_int_dec_eq(v___x_4036_, v___x_4029_);
                    lean_dec(v___x_4036_);
                    if v___x_4037_ == 0 {
                        if v___x_4034_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_year_4026_);
                            return v___x_4034_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4031_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_4032_ = lean_int_mod(v_year_4026_, v___x_4031_);
                lean_dec(v_year_4026_);
                v___x_4033_ = lean_int_dec_eq(v___x_4032_, v___x_4029_);
                lean_dec(v___x_4032_);
                return v___x_4033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear___redArg___boxed(
    mut v_date_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4039_: u8 = 0;
    let mut v_r_4040_: *mut LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_4038_);
    lean_dec_ref(v_date_4038_);
    v_r_4040_ = lean_box((v_res_4039_) as usize);
    return v_r_4040_;
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear(
    mut v_tz_4041_: *mut LeanObject,
    mut v_date_4042_: *mut LeanObject,
) -> u8 {
    let mut v___x_4043_: u8 = 0;
    v___x_4043_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear___boxed(
    mut v_tz_4044_: *mut LeanObject,
    mut v_date_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4046_: u8 = 0;
    let mut v_r_4047_: *mut LeanObject = core::ptr::null_mut();
    v_res_4046_ = l_Std_Time_DateTime_inLeapYear(v_tz_4044_, v_date_4045_);
    lean_dec_ref(v_date_4045_);
    lean_dec_ref(v_tz_4044_);
    v_r_4047_ = lean_box((v_res_4046_) as usize);
    return v_r_4047_;
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear___redArg(
    mut v_date_4048_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4051_: u8 = 0;
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v_month_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_day_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_unused_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_year_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: u8 = 0;
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4049_ = lean_ctor_get(v_date_4048_, 1);
                v___x_4065_ = lean_thunk_get_own(v_date_4049_);
                v_date_4066_ = lean_ctor_get(v___x_4065_, 0);
                lean_inc_ref(v_date_4066_);
                lean_dec(v___x_4065_);
                v_year_4067_ = lean_ctor_get(v_date_4066_, 0);
                lean_inc(v_year_4067_);
                lean_dec_ref(v_date_4066_);
                v___x_4068_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_4069_ = lean_int_mod(v_year_4067_, v___x_4068_);
                v___x_4070_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_4075_ = lean_int_dec_eq(v___x_4069_, v___x_4070_);
                lean_dec(v___x_4069_);
                if v___x_4075_ == 0 {
                    lean_dec(v_year_4067_);
                    v___y_4051_ = v___x_4075_;
                    state = 1;
                    continue;
                } else {
                    v___x_4076_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_4077_ = lean_int_mod(v_year_4067_, v___x_4076_);
                    v___x_4078_ = lean_int_dec_eq(v___x_4077_, v___x_4070_);
                    lean_dec(v___x_4077_);
                    if v___x_4078_ == 0 {
                        if v___x_4075_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_year_4067_);
                            v___y_4051_ = v___x_4075_;
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
                v___x_4052_ = lean_thunk_get_own(v_date_4049_);
                v_date_4053_ = lean_ctor_get(v___x_4052_, 0);
                v_isSharedCheck_4063_ = (!lean_is_exclusive(v___x_4052_)) as u8;
                if v_isSharedCheck_4063_ == 0 {
                    v_unused_4064_ = lean_ctor_get(v___x_4052_, 1);
                    lean_dec(v_unused_4064_);
                    v___x_4055_ = v___x_4052_;
                    v_isShared_4056_ = v_isSharedCheck_4063_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_date_4053_);
                    lean_dec(v___x_4052_);
                    v___x_4055_ = lean_box(0);
                    v_isShared_4056_ = v_isSharedCheck_4063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_4057_ = lean_ctor_get(v_date_4053_, 1);
                lean_inc(v_month_4057_);
                v_day_4058_ = lean_ctor_get(v_date_4053_, 2);
                lean_inc(v_day_4058_);
                lean_dec_ref(v_date_4053_);
                if v_isShared_4056_ == 0 {
                    lean_ctor_set(v___x_4055_, 1, v_day_4058_);
                    lean_ctor_set(v___x_4055_, 0, v_month_4057_);
                    v___x_4060_ = v___x_4055_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_month_4057_);
                    lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_day_4058_);
                    v___x_4060_ = v_reuseFailAlloc_4062_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4061_ = l_Std_Time_ValidDate_dayOfYear(v___y_4051_, v___x_4060_);
                lean_dec_ref(v___x_4060_);
                return v___x_4061_;
            }
            4 => {
                v___x_4072_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_4073_ = lean_int_mod(v_year_4067_, v___x_4072_);
                lean_dec(v_year_4067_);
                v___x_4074_ = lean_int_dec_eq(v___x_4073_, v___x_4070_);
                lean_dec(v___x_4073_);
                v___y_4051_ = v___x_4074_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear___redArg___boxed(
    mut v_date_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4080_: *mut LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_4079_);
    lean_dec_ref(v_date_4079_);
    return v_res_4080_;
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear(
    mut v_tz_4081_: *mut LeanObject,
    mut v_date_4082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    v___x_4083_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_4082_);
    return v___x_4083_;
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear___boxed(
    mut v_tz_4084_: *mut LeanObject,
    mut v_date_4085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4086_: *mut LeanObject = core::ptr::null_mut();
    v_res_4086_ = l_Std_Time_DateTime_dayOfYear(v_tz_4084_, v_date_4085_);
    lean_dec_ref(v_date_4085_);
    lean_dec_ref(v_tz_4084_);
    return v_res_4086_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear___redArg(
    mut v_date_4087_: *mut LeanObject,
    mut v_firstDay_4088_: u8,
) -> *mut LeanObject {
    let mut v_date_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v_date_4089_ = lean_ctor_get(v_date_4087_, 1);
    v___x_4090_ = lean_thunk_get_own(v_date_4089_);
    v_date_4091_ = lean_ctor_get(v___x_4090_, 0);
    lean_inc_ref(v_date_4091_);
    lean_dec(v___x_4090_);
    v___x_4092_ = l_Std_Time_PlainDate_weekOfYear(v_date_4091_, v_firstDay_4088_);
    return v___x_4092_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear___redArg___boxed(
    mut v_date_4093_: *mut LeanObject,
    mut v_firstDay_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_4095_: u8 = 0;
    let mut v_res_4096_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4095_ = (lean_unbox(v_firstDay_4094_) as u8);
    v_res_4096_ = l_Std_Time_DateTime_weekOfYear___redArg(v_date_4093_, v_firstDay_boxed_4095_);
    lean_dec_ref(v_date_4093_);
    return v_res_4096_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear(
    mut v_tz_4097_: *mut LeanObject,
    mut v_date_4098_: *mut LeanObject,
    mut v_firstDay_4099_: u8,
) -> *mut LeanObject {
    let mut v_date_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    v_date_4100_ = lean_ctor_get(v_date_4098_, 1);
    v___x_4101_ = lean_thunk_get_own(v_date_4100_);
    v_date_4102_ = lean_ctor_get(v___x_4101_, 0);
    lean_inc_ref(v_date_4102_);
    lean_dec(v___x_4101_);
    v___x_4103_ = l_Std_Time_PlainDate_weekOfYear(v_date_4102_, v_firstDay_4099_);
    return v___x_4103_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear___boxed(
    mut v_tz_4104_: *mut LeanObject,
    mut v_date_4105_: *mut LeanObject,
    mut v_firstDay_4106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_4107_: u8 = 0;
    let mut v_res_4108_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4107_ = (lean_unbox(v_firstDay_4106_) as u8);
    v_res_4108_ = l_Std_Time_DateTime_weekOfYear(v_tz_4104_, v_date_4105_, v_firstDay_boxed_4107_);
    lean_dec_ref(v_date_4105_);
    lean_dec_ref(v_tz_4104_);
    return v_res_4108_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear___redArg(
    mut v_date_4109_: *mut LeanObject,
    mut v_firstDay_4110_: u8,
) -> *mut LeanObject {
    let mut v_date_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    v_date_4111_ = lean_ctor_get(v_date_4109_, 1);
    v___x_4112_ = lean_thunk_get_own(v_date_4111_);
    v_date_4113_ = lean_ctor_get(v___x_4112_, 0);
    lean_inc_ref(v_date_4113_);
    lean_dec(v___x_4112_);
    v___x_4114_ = l_Std_Time_PlainDate_weekYear(v_date_4113_, v_firstDay_4110_);
    return v___x_4114_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear___redArg___boxed(
    mut v_date_4115_: *mut LeanObject,
    mut v_firstDay_4116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_4117_: u8 = 0;
    let mut v_res_4118_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4117_ = (lean_unbox(v_firstDay_4116_) as u8);
    v_res_4118_ = l_Std_Time_DateTime_weekYear___redArg(v_date_4115_, v_firstDay_boxed_4117_);
    lean_dec_ref(v_date_4115_);
    return v_res_4118_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear(
    mut v_tz_4119_: *mut LeanObject,
    mut v_date_4120_: *mut LeanObject,
    mut v_firstDay_4121_: u8,
) -> *mut LeanObject {
    let mut v_date_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    v_date_4122_ = lean_ctor_get(v_date_4120_, 1);
    v___x_4123_ = lean_thunk_get_own(v_date_4122_);
    v_date_4124_ = lean_ctor_get(v___x_4123_, 0);
    lean_inc_ref(v_date_4124_);
    lean_dec(v___x_4123_);
    v___x_4125_ = l_Std_Time_PlainDate_weekYear(v_date_4124_, v_firstDay_4121_);
    return v___x_4125_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear___boxed(
    mut v_tz_4126_: *mut LeanObject,
    mut v_date_4127_: *mut LeanObject,
    mut v_firstDay_4128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_4129_: u8 = 0;
    let mut v_res_4130_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4129_ = (lean_unbox(v_firstDay_4128_) as u8);
    v_res_4130_ = l_Std_Time_DateTime_weekYear(v_tz_4126_, v_date_4127_, v_firstDay_boxed_4129_);
    lean_dec_ref(v_date_4127_);
    lean_dec_ref(v_tz_4126_);
    return v_res_4130_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth___redArg(
    mut v_date_4131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    v_date_4132_ = lean_ctor_get(v_date_4131_, 1);
    v___x_4133_ = lean_thunk_get_own(v_date_4132_);
    v___x_4134_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_4133_);
    lean_dec(v___x_4133_);
    return v___x_4134_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth___redArg___boxed(
    mut v_date_4135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4136_: *mut LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_4135_);
    lean_dec_ref(v_date_4135_);
    return v_res_4136_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth(
    mut v_tz_4137_: *mut LeanObject,
    mut v_date_4138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    v___x_4139_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_4138_);
    return v___x_4139_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth___boxed(
    mut v_tz_4140_: *mut LeanObject,
    mut v_date_4141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4142_: *mut LeanObject = core::ptr::null_mut();
    v_res_4142_ = l_Std_Time_DateTime_weekOfMonth(v_tz_4140_, v_date_4141_);
    lean_dec_ref(v_date_4141_);
    lean_dec_ref(v_tz_4140_);
    return v_res_4142_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth___redArg(
    mut v_date_4143_: *mut LeanObject,
    mut v_firstDay_4144_: u8,
) -> *mut LeanObject {
    let mut v_date_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    v_date_4145_ = lean_ctor_get(v_date_4143_, 1);
    v___x_4146_ = lean_thunk_get_own(v_date_4145_);
    v_date_4147_ = lean_ctor_get(v___x_4146_, 0);
    lean_inc_ref(v_date_4147_);
    lean_dec(v___x_4146_);
    v___x_4148_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_4147_, v_firstDay_4144_);
    return v___x_4148_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(
    mut v_date_4149_: *mut LeanObject,
    mut v_firstDay_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_4151_: u8 = 0;
    let mut v_res_4152_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4151_ = (lean_unbox(v_firstDay_4150_) as u8);
    v_res_4152_ =
        l_Std_Time_DateTime_alignedWeekOfMonth___redArg(v_date_4149_, v_firstDay_boxed_4151_);
    lean_dec_ref(v_date_4149_);
    return v_res_4152_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth(
    mut v_tz_4153_: *mut LeanObject,
    mut v_date_4154_: *mut LeanObject,
    mut v_firstDay_4155_: u8,
) -> *mut LeanObject {
    let mut v_date_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    v_date_4156_ = lean_ctor_get(v_date_4154_, 1);
    v___x_4157_ = lean_thunk_get_own(v_date_4156_);
    v_date_4158_ = lean_ctor_get(v___x_4157_, 0);
    lean_inc_ref(v_date_4158_);
    lean_dec(v___x_4157_);
    v___x_4159_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_4158_, v_firstDay_4155_);
    return v___x_4159_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth___boxed(
    mut v_tz_4160_: *mut LeanObject,
    mut v_date_4161_: *mut LeanObject,
    mut v_firstDay_4162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_firstDay_boxed_4163_: u8 = 0;
    let mut v_res_4164_: *mut LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4163_ = (lean_unbox(v_firstDay_4162_) as u8);
    v_res_4164_ =
        l_Std_Time_DateTime_alignedWeekOfMonth(v_tz_4160_, v_date_4161_, v_firstDay_boxed_4163_);
    lean_dec_ref(v_date_4161_);
    lean_dec_ref(v_tz_4160_);
    return v_res_4164_;
}
pub unsafe fn l_Std_Time_DateTime_quarter___redArg(
    mut v_date_4165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    v_date_4166_ = lean_ctor_get(v_date_4165_, 1);
    v___x_4167_ = lean_thunk_get_own(v_date_4166_);
    v_date_4168_ = lean_ctor_get(v___x_4167_, 0);
    lean_inc_ref(v_date_4168_);
    lean_dec(v___x_4167_);
    v___x_4169_ = l_Std_Time_PlainDate_quarter(v_date_4168_);
    lean_dec_ref(v_date_4168_);
    return v___x_4169_;
}
pub unsafe fn l_Std_Time_DateTime_quarter___redArg___boxed(
    mut v_date_4170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4171_: *mut LeanObject = core::ptr::null_mut();
    v_res_4171_ = l_Std_Time_DateTime_quarter___redArg(v_date_4170_);
    lean_dec_ref(v_date_4170_);
    return v_res_4171_;
}
pub unsafe fn l_Std_Time_DateTime_quarter(
    mut v_tz_4172_: *mut LeanObject,
    mut v_date_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_date_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    v_date_4174_ = lean_ctor_get(v_date_4173_, 1);
    v___x_4175_ = lean_thunk_get_own(v_date_4174_);
    v_date_4176_ = lean_ctor_get(v___x_4175_, 0);
    lean_inc_ref(v_date_4176_);
    lean_dec(v___x_4175_);
    v___x_4177_ = l_Std_Time_PlainDate_quarter(v_date_4176_);
    lean_dec_ref(v_date_4176_);
    return v___x_4177_;
}
pub unsafe fn l_Std_Time_DateTime_quarter___boxed(
    mut v_tz_4178_: *mut LeanObject,
    mut v_date_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4180_: *mut LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Std_Time_DateTime_quarter(v_tz_4178_, v_date_4179_);
    lean_dec_ref(v_date_4179_);
    lean_dec_ref(v_tz_4178_);
    return v_res_4180_;
}
pub unsafe fn l_Std_Time_DateTime_time___redArg(
    mut v_zdt_4181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_4184_: *mut LeanObject = core::ptr::null_mut();
    v_date_4182_ = lean_ctor_get(v_zdt_4181_, 1);
    v___x_4183_ = lean_thunk_get_own(v_date_4182_);
    v_time_4184_ = lean_ctor_get(v___x_4183_, 1);
    lean_inc_ref(v_time_4184_);
    lean_dec(v___x_4183_);
    return v_time_4184_;
}
pub unsafe fn l_Std_Time_DateTime_time___redArg___boxed(
    mut v_zdt_4185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4186_: *mut LeanObject = core::ptr::null_mut();
    v_res_4186_ = l_Std_Time_DateTime_time___redArg(v_zdt_4185_);
    lean_dec_ref(v_zdt_4185_);
    return v_res_4186_;
}
pub unsafe fn l_Std_Time_DateTime_time(
    mut v_tz_4187_: *mut LeanObject,
    mut v_zdt_4188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_date_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_time_4191_: *mut LeanObject = core::ptr::null_mut();
    v_date_4189_ = lean_ctor_get(v_zdt_4188_, 1);
    v___x_4190_ = lean_thunk_get_own(v_date_4189_);
    v_time_4191_ = lean_ctor_get(v___x_4190_, 1);
    lean_inc_ref(v_time_4191_);
    lean_dec(v___x_4190_);
    return v_time_4191_;
}
pub unsafe fn l_Std_Time_DateTime_time___boxed(
    mut v_tz_4192_: *mut LeanObject,
    mut v_zdt_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4194_: *mut LeanObject = core::ptr::null_mut();
    v_res_4194_ = l_Std_Time_DateTime_time(v_tz_4192_, v_zdt_4193_);
    lean_dec_ref(v_zdt_4193_);
    lean_dec_ref(v_tz_4192_);
    return v_res_4194_;
}
pub unsafe fn l_Std_Time_DateTime_ofEpochDay(
    mut v_days_4195_: *mut LeanObject,
    mut v_time_4196_: *mut LeanObject,
    mut v_tz_4197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___f_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tm_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_4198_ = lean_ctor_get(v_tz_4197_, 0);
                v___x_4199_ = l_Std_Time_PlainDate_ofEpochDay(v_days_4195_);
                v___x_4200_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4200_, 0, v___x_4199_);
                lean_ctor_set(v___x_4200_, 1, v_time_4196_);
                lean_inc_ref(v___x_4200_);
                v___x_4201_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4200_);
                v_second_4202_ = lean_ctor_get(v___x_4201_, 0);
                v_nano_4203_ = lean_ctor_get(v___x_4201_, 1);
                v_isSharedCheck_4221_ = (!lean_is_exclusive(v___x_4201_)) as u8;
                if v_isSharedCheck_4221_ == 0 {
                    v___x_4205_ = v___x_4201_;
                    v_isShared_4206_ = v_isSharedCheck_4221_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nano_4203_);
                    lean_inc(v_second_4202_);
                    lean_dec(v___x_4201_);
                    v___x_4205_ = lean_box(0);
                    v_isShared_4206_ = v_isSharedCheck_4221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_4207_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_4207_, 0, v___x_4200_);
                v___x_4208_ = lean_int_neg(v_offset_4198_);
                v___x_4209_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_4210_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4211_ = lean_int_mul(v_second_4202_, v___x_4210_);
                lean_dec(v_second_4202_);
                v___x_4212_ = lean_int_add(v___x_4211_, v_nano_4203_);
                lean_dec(v_nano_4203_);
                lean_dec(v___x_4211_);
                v___x_4213_ = lean_int_mul(v___x_4208_, v___x_4210_);
                lean_dec(v___x_4208_);
                v___x_4214_ = lean_int_add(v___x_4213_, v___x_4209_);
                lean_dec(v___x_4213_);
                v___x_4215_ = lean_int_add(v___x_4212_, v___x_4214_);
                lean_dec(v___x_4214_);
                lean_dec(v___x_4212_);
                v_tm_4216_ = l_Std_Time_Duration_ofNanoseconds(v___x_4215_);
                lean_dec(v___x_4215_);
                v___x_4217_ = lean_mk_thunk(v___f_4207_);
                if v_isShared_4206_ == 0 {
                    lean_ctor_set(v___x_4205_, 1, v___x_4217_);
                    lean_ctor_set(v___x_4205_, 0, v_tm_4216_);
                    v___x_4219_ = v___x_4205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_tm_4216_);
                    lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4217_);
                    v___x_4219_ = v_reuseFailAlloc_4220_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4219_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_ofEpochDay___boxed(
    mut v_days_4222_: *mut LeanObject,
    mut v_time_4223_: *mut LeanObject,
    mut v_tz_4224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4225_: *mut LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Std_Time_DateTime_ofEpochDay(v_days_4222_, v_time_4223_, v_tz_4224_);
    lean_dec_ref(v_tz_4224_);
    lean_dec(v_days_4222_);
    return v_res_4225_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset(
    mut v_tz_4226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    v___x_4227_ = lean_alloc_closure(
        l_Std_Time_DateTime_addDays___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4227_, 0, v_tz_4226_);
    return v___x_4227_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset(
    mut v_tz_4228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    v___x_4229_ = lean_alloc_closure(
        l_Std_Time_DateTime_subDays___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4229_, 0, v_tz_4228_);
    return v___x_4229_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__1(
    mut v_tz_4230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    v___x_4231_ = lean_alloc_closure(
        l_Std_Time_DateTime_addWeeks___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4231_, 0, v_tz_4230_);
    return v___x_4231_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__1(
    mut v_tz_4232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    v___x_4233_ = lean_alloc_closure(
        l_Std_Time_DateTime_subWeeks___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4233_, 0, v_tz_4232_);
    return v___x_4233_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__2(
    mut v_tz_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    v___x_4235_ = lean_alloc_closure(
        l_Std_Time_DateTime_addHours___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4235_, 0, v_tz_4234_);
    return v___x_4235_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__2(
    mut v_tz_4236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    v___x_4237_ = lean_alloc_closure(
        l_Std_Time_DateTime_subHours___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4237_, 0, v_tz_4236_);
    return v___x_4237_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__3(
    mut v_tz_4238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    v___x_4239_ = lean_alloc_closure(
        l_Std_Time_DateTime_addMinutes___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4239_, 0, v_tz_4238_);
    return v___x_4239_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__3(
    mut v_tz_4240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    v___x_4241_ = lean_alloc_closure(
        l_Std_Time_DateTime_subMinutes___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4241_, 0, v_tz_4240_);
    return v___x_4241_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__4(
    mut v_tz_4242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    v___x_4243_ = lean_alloc_closure(
        l_Std_Time_DateTime_addSeconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4243_, 0, v_tz_4242_);
    return v___x_4243_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__4(
    mut v_tz_4244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    v___x_4245_ = lean_alloc_closure(
        l_Std_Time_DateTime_subSeconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4245_, 0, v_tz_4244_);
    return v___x_4245_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__5(
    mut v_tz_4246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    v___x_4247_ = lean_alloc_closure(
        l_Std_Time_DateTime_addMilliseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4247_, 0, v_tz_4246_);
    return v___x_4247_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__5(
    mut v_tz_4248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    v___x_4249_ = lean_alloc_closure(
        l_Std_Time_DateTime_subMilliseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4249_, 0, v_tz_4248_);
    return v___x_4249_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__6(
    mut v_tz_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    v___x_4251_ = lean_alloc_closure(
        l_Std_Time_DateTime_addNanoseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4251_, 0, v_tz_4250_);
    return v___x_4251_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__6(
    mut v_tz_4252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    v___x_4253_ = lean_alloc_closure(
        l_Std_Time_DateTime_subNanoseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___x_4253_, 0, v_tz_4252_);
    return v___x_4253_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration___lam__0(
    mut v_x_4254_: *mut LeanObject,
    mut v_y_4255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_timestamp_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    v_timestamp_4256_ = lean_ctor_get(v_y_4255_, 0);
    v_timestamp_4257_ = lean_ctor_get(v_x_4254_, 0);
    v_second_4258_ = lean_ctor_get(v_timestamp_4256_, 0);
    v_nano_4259_ = lean_ctor_get(v_timestamp_4256_, 1);
    v_second_4260_ = lean_ctor_get(v_timestamp_4257_, 0);
    v_nano_4261_ = lean_ctor_get(v_timestamp_4257_, 1);
    v___x_4262_ = lean_int_neg(v_second_4258_);
    v___x_4263_ = lean_int_neg(v_nano_4259_);
    v___x_4264_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4265_ = lean_int_mul(v_second_4260_, v___x_4264_);
    v___x_4266_ = lean_int_add(v___x_4265_, v_nano_4261_);
    lean_dec(v___x_4265_);
    v___x_4267_ = lean_int_mul(v___x_4262_, v___x_4264_);
    lean_dec(v___x_4262_);
    v___x_4268_ = lean_int_add(v___x_4267_, v___x_4263_);
    lean_dec(v___x_4263_);
    lean_dec(v___x_4267_);
    v___x_4269_ = lean_int_add(v___x_4266_, v___x_4268_);
    lean_dec(v___x_4268_);
    lean_dec(v___x_4266_);
    v___x_4270_ = l_Std_Time_Duration_ofNanoseconds(v___x_4269_);
    lean_dec(v___x_4269_);
    return v___x_4270_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(
    mut v_x_4271_: *mut LeanObject,
    mut v_y_4272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4273_: *mut LeanObject = core::ptr::null_mut();
    v_res_4273_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_4271_, v_y_4272_);
    lean_dec_ref(v_y_4272_);
    lean_dec_ref(v_x_4271_);
    return v_res_4273_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration(
    mut v_tz_4275_: *mut LeanObject,
    mut v_tz_u2081_4276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4277_: *mut LeanObject = core::ptr::null_mut();
    v___f_4277_ = l_Std_Time_DateTime_instHSubDuration___closed__0;
    return v___f_4277_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration___boxed(
    mut v_tz_4278_: *mut LeanObject,
    mut v_tz_u2081_4279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4280_: *mut LeanObject = core::ptr::null_mut();
    v_res_4280_ = l_Std_Time_DateTime_instHSubDuration(v_tz_4278_, v_tz_u2081_4279_);
    lean_dec_ref(v_tz_u2081_4279_);
    lean_dec_ref(v_tz_4278_);
    return v_res_4280_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddDuration___lam__1(
    mut v_tz_4281_: *mut LeanObject,
    mut v_x_4282_: *mut LeanObject,
    mut v_y_4283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_timestamp_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v_second_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanos_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut v_unused_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_4284_ = lean_ctor_get(v_x_4282_, 0);
                v_isSharedCheck_4309_ = (!lean_is_exclusive(v_x_4282_)) as u8;
                if v_isSharedCheck_4309_ == 0 {
                    v_unused_4310_ = lean_ctor_get(v_x_4282_, 1);
                    lean_dec(v_unused_4310_);
                    v___x_4286_ = v_x_4282_;
                    v_isShared_4287_ = v_isSharedCheck_4309_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_4284_);
                    lean_dec(v_x_4282_);
                    v___x_4286_ = lean_box(0);
                    v_isShared_4287_ = v_isSharedCheck_4309_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_4288_ = lean_ctor_get(v_y_4283_, 0);
                v_nano_4289_ = lean_ctor_get(v_y_4283_, 1);
                v_second_4290_ = lean_ctor_get(v_timestamp_4284_, 0);
                lean_inc(v_second_4290_);
                v_nano_4291_ = lean_ctor_get(v_timestamp_4284_, 1);
                lean_inc(v_nano_4291_);
                lean_dec_ref(v_timestamp_4284_);
                v___x_4292_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4293_ = lean_int_mul(v_second_4288_, v___x_4292_);
                v_nanos_4294_ = lean_int_add(v___x_4293_, v_nano_4289_);
                lean_dec(v___x_4293_);
                v___x_4295_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_4294_);
                lean_dec(v_nanos_4294_);
                v_second_4296_ = lean_ctor_get(v___x_4295_, 0);
                lean_inc(v_second_4296_);
                v_nano_4297_ = lean_ctor_get(v___x_4295_, 1);
                lean_inc(v_nano_4297_);
                lean_dec_ref(v___x_4295_);
                v___x_4298_ = lean_int_mul(v_second_4290_, v___x_4292_);
                lean_dec(v_second_4290_);
                v___x_4299_ = lean_int_add(v___x_4298_, v_nano_4291_);
                lean_dec(v_nano_4291_);
                lean_dec(v___x_4298_);
                v___x_4300_ = lean_int_mul(v_second_4296_, v___x_4292_);
                lean_dec(v_second_4296_);
                v___x_4301_ = lean_int_add(v___x_4300_, v_nano_4297_);
                lean_dec(v_nano_4297_);
                lean_dec(v___x_4300_);
                v___x_4302_ = lean_int_add(v___x_4299_, v___x_4301_);
                lean_dec(v___x_4301_);
                lean_dec(v___x_4299_);
                v___x_4303_ = l_Std_Time_Duration_ofNanoseconds(v___x_4302_);
                lean_dec(v___x_4302_);
                lean_inc_ref(v___x_4303_);
                v___f_4304_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4304_, 0, v_tz_4281_);
                lean_closure_set(v___f_4304_, 1, v___x_4303_);
                lean_closure_set(v___f_4304_, 2, v___x_4292_);
                v___x_4305_ = lean_mk_thunk(v___f_4304_);
                if v_isShared_4287_ == 0 {
                    lean_ctor_set(v___x_4286_, 1, v___x_4305_);
                    lean_ctor_set(v___x_4286_, 0, v___x_4303_);
                    v___x_4307_ = v___x_4286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4303_);
                    lean_ctor_set(v_reuseFailAlloc_4308_, 1, v___x_4305_);
                    v___x_4307_ = v_reuseFailAlloc_4308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_instHAddDuration___lam__1___boxed(
    mut v_tz_4311_: *mut LeanObject,
    mut v_x_4312_: *mut LeanObject,
    mut v_y_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4314_: *mut LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_Std_Time_DateTime_instHAddDuration___lam__1(v_tz_4311_, v_x_4312_, v_y_4313_);
    lean_dec_ref(v_y_4313_);
    return v_res_4314_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddDuration(
    mut v_tz_4315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4316_: *mut LeanObject = core::ptr::null_mut();
    v___f_4316_ = lean_alloc_closure(
        l_Std_Time_DateTime_instHAddDuration___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4316_, 0, v_tz_4315_);
    return v___f_4316_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration__1___lam__1(
    mut v_tz_4317_: *mut LeanObject,
    mut v_x_4318_: *mut LeanObject,
    mut v_y_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_second_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_timestamp_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nanos_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nano_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_unused_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_4320_ = lean_ctor_get(v_y_4319_, 0);
                v_nano_4321_ = lean_ctor_get(v_y_4319_, 1);
                v_timestamp_4322_ = lean_ctor_get(v_x_4318_, 0);
                v_isSharedCheck_4347_ = (!lean_is_exclusive(v_x_4318_)) as u8;
                if v_isSharedCheck_4347_ == 0 {
                    v_unused_4348_ = lean_ctor_get(v_x_4318_, 1);
                    lean_dec(v_unused_4348_);
                    v___x_4324_ = v_x_4318_;
                    v_isShared_4325_ = v_isSharedCheck_4347_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_timestamp_4322_);
                    lean_dec(v_x_4318_);
                    v___x_4324_ = lean_box(0);
                    v_isShared_4325_ = v_isSharedCheck_4347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4326_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4327_ = lean_int_mul(v_second_4320_, v___x_4326_);
                v_nanos_4328_ = lean_int_add(v___x_4327_, v_nano_4321_);
                lean_dec(v___x_4327_);
                v___x_4329_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_4328_);
                lean_dec(v_nanos_4328_);
                v_second_4330_ = lean_ctor_get(v___x_4329_, 0);
                lean_inc(v_second_4330_);
                v_nano_4331_ = lean_ctor_get(v___x_4329_, 1);
                lean_inc(v_nano_4331_);
                lean_dec_ref(v___x_4329_);
                v_second_4332_ = lean_ctor_get(v_timestamp_4322_, 0);
                lean_inc(v_second_4332_);
                v_nano_4333_ = lean_ctor_get(v_timestamp_4322_, 1);
                lean_inc(v_nano_4333_);
                lean_dec_ref(v_timestamp_4322_);
                v___x_4334_ = lean_int_neg(v_second_4330_);
                lean_dec(v_second_4330_);
                v___x_4335_ = lean_int_neg(v_nano_4331_);
                lean_dec(v_nano_4331_);
                v___x_4336_ = lean_int_mul(v_second_4332_, v___x_4326_);
                lean_dec(v_second_4332_);
                v___x_4337_ = lean_int_add(v___x_4336_, v_nano_4333_);
                lean_dec(v_nano_4333_);
                lean_dec(v___x_4336_);
                v___x_4338_ = lean_int_mul(v___x_4334_, v___x_4326_);
                lean_dec(v___x_4334_);
                v___x_4339_ = lean_int_add(v___x_4338_, v___x_4335_);
                lean_dec(v___x_4335_);
                lean_dec(v___x_4338_);
                v___x_4340_ = lean_int_add(v___x_4337_, v___x_4339_);
                lean_dec(v___x_4339_);
                lean_dec(v___x_4337_);
                v___x_4341_ = l_Std_Time_Duration_ofNanoseconds(v___x_4340_);
                lean_dec(v___x_4340_);
                lean_inc_ref(v___x_4341_);
                v___f_4342_ = lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                lean_closure_set(v___f_4342_, 0, v_tz_4317_);
                lean_closure_set(v___f_4342_, 1, v___x_4341_);
                lean_closure_set(v___f_4342_, 2, v___x_4326_);
                v___x_4343_ = lean_mk_thunk(v___f_4342_);
                if v_isShared_4325_ == 0 {
                    lean_ctor_set(v___x_4324_, 1, v___x_4343_);
                    lean_ctor_set(v___x_4324_, 0, v___x_4341_);
                    v___x_4345_ = v___x_4324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4341_);
                    lean_ctor_set(v_reuseFailAlloc_4346_, 1, v___x_4343_);
                    v___x_4345_ = v_reuseFailAlloc_4346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed(
    mut v_tz_4349_: *mut LeanObject,
    mut v_x_4350_: *mut LeanObject,
    mut v_y_4351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4352_: *mut LeanObject = core::ptr::null_mut();
    v_res_4352_ =
        l_Std_Time_DateTime_instHSubDuration__1___lam__1(v_tz_4349_, v_x_4350_, v_y_4351_);
    lean_dec_ref(v_y_4351_);
    return v_res_4352_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration__1(
    mut v_tz_4353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4354_: *mut LeanObject = core::ptr::null_mut();
    v___f_4354_ = lean_alloc_closure(
        l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_4354_, 0, v_tz_4353_);
    return v___f_4354_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
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
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_TimeZone(builtin);
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
    res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Zoned_DateTime(builtin);
}
