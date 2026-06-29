// Lean compiler output
// Module: Std.Time.Zoned.DateTime
// Imports: Std.Time.DateTime Std.Time.Zoned.TimeZone Std.Time.Date.Unit.Month Std.Time.Date.Unit.Year Std.Time.DateTime.PlainDateTime
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_lt, lean_int_emod, lean_int_mod, lean_int_mul,
    lean_int_neg, lean_mk_thunk, lean_nat_to_int, lean_thunk_get_own,
};
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
pub static l_Std_Time_instBEqDateTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instBEqDateTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instBEqDateTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instBEqDateTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_Time_instOrdDateTime___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_Time_instOrdDateTime___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_instOrdDateTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_instOrdDateTime___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_Time_instOrdDateTime___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_instOrdDateTime___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_ofPlainDateTime___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_ofPlainDateTime___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_addHours___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_addHours___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_addMinutes___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_addMinutes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_addMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_addMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_addDays___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_addDays___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_addWeeks___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_addWeeks___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_addYearsRollOver___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_addYearsRollOver___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_withDaysClip___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_withDaysClip___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_withDaysClip___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_withDaysClip___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_withDaysClip___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_withDaysClip___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Std_Time_DateTime_withMilliseconds___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_DateTime_withMilliseconds___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_DateTime_instHSubDuration___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Std_Time_DateTime_instHSubDuration___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_DateTime_instHSubDuration___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_DateTime_instHSubDuration___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_Time_instBEqDateTime___lam__0(
    mut v_x_2178_: *mut crate::leanh::LeanObject,
    mut v_y_2179_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_timestamp_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timestamp_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: u8 = 0;
    v_timestamp_2180_ = crate::leanh::lean_ctor_get(v_x_2178_, 0);
    v_timestamp_2181_ = crate::leanh::lean_ctor_get(v_y_2179_, 0);
    v___x_2182_ = l_Std_Time_instDecidableEqDuration_decEq(v_timestamp_2180_, v_timestamp_2181_);
    return v___x_2182_;
}
pub unsafe fn l_Std_Time_instBEqDateTime___lam__0___boxed(
    mut v_x_2183_: *mut crate::leanh::LeanObject,
    mut v_y_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2185_: u8 = 0;
    let mut v_r_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Std_Time_instBEqDateTime___lam__0(v_x_2183_, v_y_2184_);
    crate::leanh::lean_dec_ref(v_y_2184_);
    crate::leanh::lean_dec_ref(v_x_2183_);
    v_r_2186_ = crate::leanh::lean_box((v_res_2185_) as usize);
    return v_r_2186_;
}
pub unsafe fn l_Std_Time_instBEqDateTime(
    mut v_tz_2188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2189_ = l_Std_Time_instBEqDateTime___closed__0;
    return v___f_2189_;
}
pub unsafe fn l_Std_Time_instBEqDateTime___boxed(
    mut v_tz_2190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2191_ = l_Std_Time_instBEqDateTime(v_tz_2190_);
    crate::leanh::lean_dec_ref(v_tz_2190_);
    return v_res_2191_;
}
pub unsafe fn l_Std_Time_instOrdDateTime___lam__0(
    mut v_x_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_2193_ = crate::leanh::lean_ctor_get(v_x_2192_, 0);
    crate::leanh::lean_inc_ref(v_timestamp_2193_);
    return v_timestamp_2193_;
}
pub unsafe fn l_Std_Time_instOrdDateTime___lam__0___boxed(
    mut v_x_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2195_ = l_Std_Time_instOrdDateTime___lam__0(v_x_2194_);
    crate::leanh::lean_dec_ref(v_x_2194_);
    return v_res_2195_;
}
pub unsafe fn _init_l_Std_Time_instOrdDateTime___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___f_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2197_ = l_Std_Time_instOrdDateTime___closed__0;
    v___x_2198_ = l_Std_Time_instOrdTimestamp;
    v___x_2199_ =
        crate::leanh::lean_alloc_closure(l_compareOn___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_2199_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2199_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2199_, 2, v___x_2198_);
    crate::leanh::lean_closure_set(v___x_2199_, 3, v___f_2197_);
    return v___x_2199_;
}
pub unsafe fn l_Std_Time_instOrdDateTime(
    mut v_tz_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2201_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_instOrdDateTime___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_instOrdDateTime___closed__1_once),
        _init_l_Std_Time_instOrdDateTime___closed__1,
    );
    return v___x_2201_;
}
pub unsafe fn l_Std_Time_instOrdDateTime___boxed(
    mut v_tz_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2203_ = l_Std_Time_instOrdDateTime(v_tz_2202_);
    crate::leanh::lean_dec_ref(v_tz_2202_);
    return v_res_2203_;
}
pub unsafe fn _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2204_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2205_ = lean_nat_to_int(v___x_2204_);
    return v___x_2205_;
}
pub unsafe fn _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2206_ = crate::leanh::lean_unsigned_to_nat(1000000000);
    v___x_2207_ = lean_nat_to_int(v___x_2206_);
    return v___x_2207_;
}
pub unsafe fn l_Std_Time_DateTime_ofTimestamp___lam__0(
    mut v_tz_2208_: *mut crate::leanh::LeanObject,
    mut v_tm_2209_: *mut crate::leanh::LeanObject,
    mut v_x_2210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2211_ = crate::leanh::lean_ctor_get(v_tz_2208_, 0);
    v_second_2212_ = crate::leanh::lean_ctor_get(v_tm_2209_, 0);
    v_nano_2213_ = crate::leanh::lean_ctor_get(v_tm_2209_, 1);
    v___x_2214_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2215_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2216_ = lean_int_mul(v_second_2212_, v___x_2215_);
    v___x_2217_ = lean_int_add(v___x_2216_, v_nano_2213_);
    crate::leanh::lean_dec(v___x_2216_);
    v___x_2218_ = lean_int_mul(v_offset_2211_, v___x_2215_);
    v___x_2219_ = lean_int_add(v___x_2218_, v___x_2214_);
    crate::leanh::lean_dec(v___x_2218_);
    v___x_2220_ = lean_int_add(v___x_2217_, v___x_2219_);
    crate::leanh::lean_dec(v___x_2219_);
    crate::leanh::lean_dec(v___x_2217_);
    v___x_2221_ = l_Std_Time_Duration_ofNanoseconds(v___x_2220_);
    crate::leanh::lean_dec(v___x_2220_);
    v___x_2222_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2221_);
    return v___x_2222_;
}
pub unsafe fn l_Std_Time_DateTime_ofTimestamp___lam__0___boxed(
    mut v_tz_2223_: *mut crate::leanh::LeanObject,
    mut v_tm_2224_: *mut crate::leanh::LeanObject,
    mut v_x_2225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2226_ = l_Std_Time_DateTime_ofTimestamp___lam__0(v_tz_2223_, v_tm_2224_, v_x_2225_);
    crate::leanh::lean_dec_ref(v_tm_2224_);
    crate::leanh::lean_dec_ref(v_tz_2223_);
    return v_res_2226_;
}
pub unsafe fn l_Std_Time_DateTime_ofTimestamp(
    mut v_tm_2227_: *mut crate::leanh::LeanObject,
    mut v_tz_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_tm_2227_);
    v___f_2229_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_ofTimestamp___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2229_, 0, v_tz_2228_);
    crate::leanh::lean_closure_set(v___f_2229_, 1, v_tm_2227_);
    v___x_2230_ = lean_mk_thunk(v___f_2229_);
    v___x_2231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2231_, 0, v_tm_2227_);
    crate::leanh::lean_ctor_set(v___x_2231_, 1, v___x_2230_);
    return v___x_2231_;
}
pub unsafe fn l_Std_Time_DateTime_instInhabited___lam__0(
    mut v_tz_2232_: *mut crate::leanh::LeanObject,
    mut v___x_2233_: *mut crate::leanh::LeanObject,
    mut v_x_2234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2235_ = crate::leanh::lean_ctor_get(v_tz_2232_, 0);
    v_second_2236_ = crate::leanh::lean_ctor_get(v___x_2233_, 0);
    v_nano_2237_ = crate::leanh::lean_ctor_get(v___x_2233_, 1);
    v___x_2238_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2239_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2240_ = lean_int_mul(v_second_2236_, v___x_2239_);
    v___x_2241_ = lean_int_add(v___x_2240_, v_nano_2237_);
    crate::leanh::lean_dec(v___x_2240_);
    v___x_2242_ = lean_int_mul(v_offset_2235_, v___x_2239_);
    v___x_2243_ = lean_int_add(v___x_2242_, v___x_2238_);
    crate::leanh::lean_dec(v___x_2242_);
    v___x_2244_ = lean_int_add(v___x_2241_, v___x_2243_);
    crate::leanh::lean_dec(v___x_2243_);
    crate::leanh::lean_dec(v___x_2241_);
    v___x_2245_ = l_Std_Time_Duration_ofNanoseconds(v___x_2244_);
    crate::leanh::lean_dec(v___x_2244_);
    v___x_2246_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2245_);
    return v___x_2246_;
}
pub unsafe fn l_Std_Time_DateTime_instInhabited___lam__0___boxed(
    mut v_tz_2247_: *mut crate::leanh::LeanObject,
    mut v___x_2248_: *mut crate::leanh::LeanObject,
    mut v_x_2249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2250_ = l_Std_Time_DateTime_instInhabited___lam__0(v_tz_2247_, v___x_2248_, v_x_2249_);
    crate::leanh::lean_dec_ref(v___x_2248_);
    crate::leanh::lean_dec_ref(v_tz_2247_);
    return v_res_2250_;
}
pub unsafe fn l_Std_Time_DateTime_instInhabited(
    mut v_tz_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = l_Std_Time_instInhabitedTimestamp_default;
    v___f_2253_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_instInhabited___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2253_, 0, v_tz_2251_);
    crate::leanh::lean_closure_set(v___f_2253_, 1, v___x_2252_);
    v___x_2254_ = lean_mk_thunk(v___f_2253_);
    v___x_2255_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2255_, 0, v___x_2252_);
    crate::leanh::lean_ctor_set(v___x_2255_, 1, v___x_2254_);
    return v___x_2255_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay___redArg(
    mut v_date_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_2257_ = crate::leanh::lean_ctor_get(v_date_2256_, 1);
    v___x_2258_ = lean_thunk_get_own(v_date_2257_);
    v_date_2259_ = crate::leanh::lean_ctor_get(v___x_2258_, 0);
    crate::leanh::lean_inc_ref(v_date_2259_);
    crate::leanh::lean_dec(v___x_2258_);
    v___x_2260_ = l_Std_Time_PlainDate_toEpochDay(v_date_2259_);
    return v___x_2260_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay___redArg___boxed(
    mut v_date_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2262_ = l_Std_Time_DateTime_toEpochDay___redArg(v_date_2261_);
    crate::leanh::lean_dec_ref(v_date_2261_);
    return v_res_2262_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay(
    mut v_tz_2263_: *mut crate::leanh::LeanObject,
    mut v_date_2264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2265_ = l_Std_Time_DateTime_toEpochDay___redArg(v_date_2264_);
    return v___x_2265_;
}
pub unsafe fn l_Std_Time_DateTime_toEpochDay___boxed(
    mut v_tz_2266_: *mut crate::leanh::LeanObject,
    mut v_date_2267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Std_Time_DateTime_toEpochDay(v_tz_2266_, v_date_2267_);
    crate::leanh::lean_dec_ref(v_date_2267_);
    crate::leanh::lean_dec_ref(v_tz_2266_);
    return v_res_2268_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp___redArg(
    mut v_date_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_2270_ = crate::leanh::lean_ctor_get(v_date_2269_, 0);
    crate::leanh::lean_inc_ref(v_timestamp_2270_);
    return v_timestamp_2270_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp___redArg___boxed(
    mut v_date_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2272_ = l_Std_Time_DateTime_toTimestamp___redArg(v_date_2271_);
    crate::leanh::lean_dec_ref(v_date_2271_);
    return v_res_2272_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp(
    mut v_tz_2273_: *mut crate::leanh::LeanObject,
    mut v_date_2274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_2275_ = crate::leanh::lean_ctor_get(v_date_2274_, 0);
    crate::leanh::lean_inc_ref(v_timestamp_2275_);
    return v_timestamp_2275_;
}
pub unsafe fn l_Std_Time_DateTime_toTimestamp___boxed(
    mut v_tz_2276_: *mut crate::leanh::LeanObject,
    mut v_date_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Std_Time_DateTime_toTimestamp(v_tz_2276_, v_date_2277_);
    crate::leanh::lean_dec_ref(v_date_2277_);
    crate::leanh::lean_dec_ref(v_tz_2276_);
    return v_res_2278_;
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(
    mut v_tz_u2081_2279_: *mut crate::leanh::LeanObject,
    mut v_timestamp_2280_: *mut crate::leanh::LeanObject,
    mut v_x_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2282_ = crate::leanh::lean_ctor_get(v_tz_u2081_2279_, 0);
    v_second_2283_ = crate::leanh::lean_ctor_get(v_timestamp_2280_, 0);
    v_nano_2284_ = crate::leanh::lean_ctor_get(v_timestamp_2280_, 1);
    v___x_2285_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2286_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_2287_ = lean_int_mul(v_second_2283_, v___x_2286_);
    v___x_2288_ = lean_int_add(v___x_2287_, v_nano_2284_);
    crate::leanh::lean_dec(v___x_2287_);
    v___x_2289_ = lean_int_mul(v_offset_2282_, v___x_2286_);
    v___x_2290_ = lean_int_add(v___x_2289_, v___x_2285_);
    crate::leanh::lean_dec(v___x_2289_);
    v___x_2291_ = lean_int_add(v___x_2288_, v___x_2290_);
    crate::leanh::lean_dec(v___x_2290_);
    crate::leanh::lean_dec(v___x_2288_);
    v___x_2292_ = l_Std_Time_Duration_ofNanoseconds(v___x_2291_);
    crate::leanh::lean_dec(v___x_2291_);
    v___x_2293_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2292_);
    return v___x_2293_;
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed(
    mut v_tz_u2081_2294_: *mut crate::leanh::LeanObject,
    mut v_timestamp_2295_: *mut crate::leanh::LeanObject,
    mut v_x_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2297_ = l_Std_Time_DateTime_convertTimeZone___redArg___lam__0(
        v_tz_u2081_2294_,
        v_timestamp_2295_,
        v_x_2296_,
    );
    crate::leanh::lean_dec_ref(v_timestamp_2295_);
    crate::leanh::lean_dec_ref(v_tz_u2081_2294_);
    return v_res_2297_;
}
pub unsafe fn l_Std_Time_DateTime_convertTimeZone___redArg(
    mut v_date_2298_: *mut crate::leanh::LeanObject,
    mut v_tz_u2081_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2303_: u8 = 0;
    let mut v___f_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v_unused_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2300_ = crate::leanh::lean_ctor_get(v_date_2298_, 0);
                v_isSharedCheck_2309_ = (!crate::leanh::lean_is_exclusive(v_date_2298_)) as u8;
                if v_isSharedCheck_2309_ == 0 {
                    v_unused_2310_ = crate::leanh::lean_ctor_get(v_date_2298_, 1);
                    crate::leanh::lean_dec(v_unused_2310_);
                    v___x_2302_ = v_date_2298_;
                    v_isShared_2303_ = v_isSharedCheck_2309_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2300_);
                    crate::leanh::lean_dec(v_date_2298_);
                    v___x_2302_ = crate::leanh::lean_box(0);
                    v_isShared_2303_ = v_isSharedCheck_2309_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_timestamp_2300_);
                v___f_2304_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2304_, 0, v_tz_u2081_2299_);
                crate::leanh::lean_closure_set(v___f_2304_, 1, v_timestamp_2300_);
                v___x_2305_ = lean_mk_thunk(v___f_2304_);
                if v_isShared_2303_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2302_, 1, v___x_2305_);
                    v___x_2307_ = v___x_2302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_timestamp_2300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2305_);
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
    mut v_tz_2311_: *mut crate::leanh::LeanObject,
    mut v_date_2312_: *mut crate::leanh::LeanObject,
    mut v_tz_u2081_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___f_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2323_: u8 = 0;
    let mut v_unused_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2314_ = crate::leanh::lean_ctor_get(v_date_2312_, 0);
                v_isSharedCheck_2323_ = (!crate::leanh::lean_is_exclusive(v_date_2312_)) as u8;
                if v_isSharedCheck_2323_ == 0 {
                    v_unused_2324_ = crate::leanh::lean_ctor_get(v_date_2312_, 1);
                    crate::leanh::lean_dec(v_unused_2324_);
                    v___x_2316_ = v_date_2312_;
                    v_isShared_2317_ = v_isSharedCheck_2323_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2314_);
                    crate::leanh::lean_dec(v_date_2312_);
                    v___x_2316_ = crate::leanh::lean_box(0);
                    v_isShared_2317_ = v_isSharedCheck_2323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_timestamp_2314_);
                v___f_2318_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_convertTimeZone___redArg___lam__0___boxed
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2318_, 0, v_tz_u2081_2313_);
                crate::leanh::lean_closure_set(v___f_2318_, 1, v_timestamp_2314_);
                v___x_2319_ = lean_mk_thunk(v___f_2318_);
                if v_isShared_2317_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2316_, 1, v___x_2319_);
                    v___x_2321_ = v___x_2316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_timestamp_2314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 1, v___x_2319_);
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
    mut v_tz_2325_: *mut crate::leanh::LeanObject,
    mut v_date_2326_: *mut crate::leanh::LeanObject,
    mut v_tz_u2081_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Std_Time_DateTime_convertTimeZone(v_tz_2325_, v_date_2326_, v_tz_u2081_2327_);
    crate::leanh::lean_dec_ref(v_tz_2325_);
    return v_res_2328_;
}
pub unsafe fn l_Std_Time_DateTime_ofPlainDateTime___lam__0(
    mut v_date_2329_: *mut crate::leanh::LeanObject,
    mut v_x_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_date_2329_);
    return v_date_2329_;
}
pub unsafe fn l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed(
    mut v_date_2331_: *mut crate::leanh::LeanObject,
    mut v_x_2332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2333_ = l_Std_Time_DateTime_ofPlainDateTime___lam__0(v_date_2331_, v_x_2332_);
    crate::leanh::lean_dec_ref(v_date_2331_);
    return v_res_2333_;
}
pub unsafe fn _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2335_ = lean_int_neg(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn l_Std_Time_DateTime_ofPlainDateTime(
    mut v_date_2336_: *mut crate::leanh::LeanObject,
    mut v_tz_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v___f_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_2338_ = crate::leanh::lean_ctor_get(v_tz_2337_, 0);
                crate::leanh::lean_inc_ref(v_date_2336_);
                v___x_2339_ = l_Std_Time_PlainDateTime_toWallTime(v_date_2336_);
                v_second_2340_ = crate::leanh::lean_ctor_get(v___x_2339_, 0);
                v_nano_2341_ = crate::leanh::lean_ctor_get(v___x_2339_, 1);
                v_isSharedCheck_2359_ = (!crate::leanh::lean_is_exclusive(v___x_2339_)) as u8;
                if v_isSharedCheck_2359_ == 0 {
                    v___x_2343_ = v___x_2339_;
                    v_isShared_2344_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_2341_);
                    crate::leanh::lean_inc(v_second_2340_);
                    crate::leanh::lean_dec(v___x_2339_);
                    v___x_2343_ = crate::leanh::lean_box(0);
                    v_isShared_2344_ = v_isSharedCheck_2359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_2345_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_ofPlainDateTime___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2345_, 0, v_date_2336_);
                v___x_2346_ = lean_int_neg(v_offset_2338_);
                v___x_2347_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2348_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2349_ = lean_int_mul(v_second_2340_, v___x_2348_);
                crate::leanh::lean_dec(v_second_2340_);
                v___x_2350_ = lean_int_add(v___x_2349_, v_nano_2341_);
                crate::leanh::lean_dec(v_nano_2341_);
                crate::leanh::lean_dec(v___x_2349_);
                v___x_2351_ = lean_int_mul(v___x_2346_, v___x_2348_);
                crate::leanh::lean_dec(v___x_2346_);
                v___x_2352_ = lean_int_add(v___x_2351_, v___x_2347_);
                crate::leanh::lean_dec(v___x_2351_);
                v___x_2353_ = lean_int_add(v___x_2350_, v___x_2352_);
                crate::leanh::lean_dec(v___x_2352_);
                crate::leanh::lean_dec(v___x_2350_);
                v_tm_2354_ = l_Std_Time_Duration_ofNanoseconds(v___x_2353_);
                crate::leanh::lean_dec(v___x_2353_);
                v___x_2355_ = lean_mk_thunk(v___f_2345_);
                if v_isShared_2344_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2343_, 1, v___x_2355_);
                    crate::leanh::lean_ctor_set(v___x_2343_, 0, v_tm_2354_);
                    v___x_2357_ = v___x_2343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_tm_2354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2355_);
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
    mut v_date_2360_: *mut crate::leanh::LeanObject,
    mut v_tz_2361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2362_ = l_Std_Time_DateTime_ofPlainDateTime(v_date_2360_, v_tz_2361_);
    crate::leanh::lean_dec_ref(v_tz_2361_);
    return v_res_2362_;
}
pub unsafe fn l_Std_Time_DateTime_addHours___lam__0(
    mut v_tz_2363_: *mut crate::leanh::LeanObject,
    mut v___x_2364_: *mut crate::leanh::LeanObject,
    mut v___x_2365_: *mut crate::leanh::LeanObject,
    mut v___x_2366_: *mut crate::leanh::LeanObject,
    mut v_x_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2368_ = crate::leanh::lean_ctor_get(v_tz_2363_, 0);
    v_second_2369_ = crate::leanh::lean_ctor_get(v___x_2364_, 0);
    v_nano_2370_ = crate::leanh::lean_ctor_get(v___x_2364_, 1);
    v___x_2371_ = lean_int_mul(v_second_2369_, v___x_2365_);
    v___x_2372_ = lean_int_add(v___x_2371_, v_nano_2370_);
    crate::leanh::lean_dec(v___x_2371_);
    v___x_2373_ = lean_int_mul(v_offset_2368_, v___x_2365_);
    v___x_2374_ = lean_int_add(v___x_2373_, v___x_2366_);
    crate::leanh::lean_dec(v___x_2373_);
    v___x_2375_ = lean_int_add(v___x_2372_, v___x_2374_);
    crate::leanh::lean_dec(v___x_2374_);
    crate::leanh::lean_dec(v___x_2372_);
    v___x_2376_ = l_Std_Time_Duration_ofNanoseconds(v___x_2375_);
    crate::leanh::lean_dec(v___x_2375_);
    v___x_2377_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2376_);
    return v___x_2377_;
}
pub unsafe fn l_Std_Time_DateTime_addHours___lam__0___boxed(
    mut v_tz_2378_: *mut crate::leanh::LeanObject,
    mut v___x_2379_: *mut crate::leanh::LeanObject,
    mut v___x_2380_: *mut crate::leanh::LeanObject,
    mut v___x_2381_: *mut crate::leanh::LeanObject,
    mut v_x_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Std_Time_DateTime_addHours___lam__0(
        v_tz_2378_,
        v___x_2379_,
        v___x_2380_,
        v___x_2381_,
        v_x_2382_,
    );
    crate::leanh::lean_dec(v___x_2381_);
    crate::leanh::lean_dec(v___x_2380_);
    crate::leanh::lean_dec_ref(v___x_2379_);
    crate::leanh::lean_dec_ref(v_tz_2378_);
    return v_res_2383_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addHours___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2384_ = crate::leanh::lean_unsigned_to_nat(3600);
    v___x_2385_ = lean_nat_to_int(v___x_2384_);
    return v___x_2385_;
}
pub unsafe fn l_Std_Time_DateTime_addHours(
    mut v_tz_2386_: *mut crate::leanh::LeanObject,
    mut v_dt_2387_: *mut crate::leanh::LeanObject,
    mut v_hours_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v_second_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_unused_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2389_ = crate::leanh::lean_ctor_get(v_dt_2387_, 0);
                v_isSharedCheck_2410_ = (!crate::leanh::lean_is_exclusive(v_dt_2387_)) as u8;
                if v_isSharedCheck_2410_ == 0 {
                    v_unused_2411_ = crate::leanh::lean_ctor_get(v_dt_2387_, 1);
                    crate::leanh::lean_dec(v_unused_2411_);
                    v___x_2391_ = v_dt_2387_;
                    v_isShared_2392_ = v_isSharedCheck_2410_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2389_);
                    crate::leanh::lean_dec(v_dt_2387_);
                    v___x_2391_ = crate::leanh::lean_box(0);
                    v_isShared_2392_ = v_isSharedCheck_2410_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2393_ = crate::leanh::lean_ctor_get(v_timestamp_2389_, 0);
                crate::leanh::lean_inc(v_second_2393_);
                v_nano_2394_ = crate::leanh::lean_ctor_get(v_timestamp_2389_, 1);
                crate::leanh::lean_inc(v_nano_2394_);
                crate::leanh::lean_dec_ref(v_timestamp_2389_);
                v___x_2395_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0_once),
                    _init_l_Std_Time_DateTime_addHours___closed__0,
                );
                v___x_2396_ = lean_int_mul(v_hours_2388_, v___x_2395_);
                v___x_2397_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2398_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2399_ = lean_int_mul(v_second_2393_, v___x_2398_);
                crate::leanh::lean_dec(v_second_2393_);
                v___x_2400_ = lean_int_add(v___x_2399_, v_nano_2394_);
                crate::leanh::lean_dec(v_nano_2394_);
                crate::leanh::lean_dec(v___x_2399_);
                v___x_2401_ = lean_int_mul(v___x_2396_, v___x_2398_);
                crate::leanh::lean_dec(v___x_2396_);
                v___x_2402_ = lean_int_add(v___x_2401_, v___x_2397_);
                crate::leanh::lean_dec(v___x_2401_);
                v___x_2403_ = lean_int_add(v___x_2400_, v___x_2402_);
                crate::leanh::lean_dec(v___x_2402_);
                crate::leanh::lean_dec(v___x_2400_);
                v___x_2404_ = l_Std_Time_Duration_ofNanoseconds(v___x_2403_);
                crate::leanh::lean_dec(v___x_2403_);
                crate::leanh::lean_inc_ref(v___x_2404_);
                v___f_2405_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2405_, 0, v_tz_2386_);
                crate::leanh::lean_closure_set(v___f_2405_, 1, v___x_2404_);
                crate::leanh::lean_closure_set(v___f_2405_, 2, v___x_2398_);
                crate::leanh::lean_closure_set(v___f_2405_, 3, v___x_2397_);
                v___x_2406_ = lean_mk_thunk(v___f_2405_);
                if v_isShared_2392_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2391_, 1, v___x_2406_);
                    crate::leanh::lean_ctor_set(v___x_2391_, 0, v___x_2404_);
                    v___x_2408_ = v___x_2391_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v___x_2404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 1, v___x_2406_);
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
    mut v_tz_2412_: *mut crate::leanh::LeanObject,
    mut v_dt_2413_: *mut crate::leanh::LeanObject,
    mut v_hours_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2415_ = l_Std_Time_DateTime_addHours(v_tz_2412_, v_dt_2413_, v_hours_2414_);
    crate::leanh::lean_dec(v_hours_2414_);
    return v_res_2415_;
}
pub unsafe fn l_Std_Time_DateTime_subHours(
    mut v_tz_2416_: *mut crate::leanh::LeanObject,
    mut v_dt_2417_: *mut crate::leanh::LeanObject,
    mut v_hours_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v_second_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut v_unused_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2419_ = crate::leanh::lean_ctor_get(v_dt_2417_, 0);
                v_isSharedCheck_2442_ = (!crate::leanh::lean_is_exclusive(v_dt_2417_)) as u8;
                if v_isSharedCheck_2442_ == 0 {
                    v_unused_2443_ = crate::leanh::lean_ctor_get(v_dt_2417_, 1);
                    crate::leanh::lean_dec(v_unused_2443_);
                    v___x_2421_ = v_dt_2417_;
                    v_isShared_2422_ = v_isSharedCheck_2442_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2419_);
                    crate::leanh::lean_dec(v_dt_2417_);
                    v___x_2421_ = crate::leanh::lean_box(0);
                    v_isShared_2422_ = v_isSharedCheck_2442_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2423_ = crate::leanh::lean_ctor_get(v_timestamp_2419_, 0);
                crate::leanh::lean_inc(v_second_2423_);
                v_nano_2424_ = crate::leanh::lean_ctor_get(v_timestamp_2419_, 1);
                crate::leanh::lean_inc(v_nano_2424_);
                crate::leanh::lean_dec_ref(v_timestamp_2419_);
                v___x_2425_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addHours___closed__0_once),
                    _init_l_Std_Time_DateTime_addHours___closed__0,
                );
                v___x_2426_ = lean_int_mul(v_hours_2418_, v___x_2425_);
                v___x_2427_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2428_ = lean_int_neg(v___x_2426_);
                crate::leanh::lean_dec(v___x_2426_);
                v___x_2429_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2430_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2431_ = lean_int_mul(v_second_2423_, v___x_2430_);
                crate::leanh::lean_dec(v_second_2423_);
                v___x_2432_ = lean_int_add(v___x_2431_, v_nano_2424_);
                crate::leanh::lean_dec(v_nano_2424_);
                crate::leanh::lean_dec(v___x_2431_);
                v___x_2433_ = lean_int_mul(v___x_2428_, v___x_2430_);
                crate::leanh::lean_dec(v___x_2428_);
                v___x_2434_ = lean_int_add(v___x_2433_, v___x_2429_);
                crate::leanh::lean_dec(v___x_2433_);
                v___x_2435_ = lean_int_add(v___x_2432_, v___x_2434_);
                crate::leanh::lean_dec(v___x_2434_);
                crate::leanh::lean_dec(v___x_2432_);
                v___x_2436_ = l_Std_Time_Duration_ofNanoseconds(v___x_2435_);
                crate::leanh::lean_dec(v___x_2435_);
                crate::leanh::lean_inc_ref(v___x_2436_);
                v___f_2437_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2437_, 0, v_tz_2416_);
                crate::leanh::lean_closure_set(v___f_2437_, 1, v___x_2436_);
                crate::leanh::lean_closure_set(v___f_2437_, 2, v___x_2430_);
                crate::leanh::lean_closure_set(v___f_2437_, 3, v___x_2427_);
                v___x_2438_ = lean_mk_thunk(v___f_2437_);
                if v_isShared_2422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2421_, 1, v___x_2438_);
                    crate::leanh::lean_ctor_set(v___x_2421_, 0, v___x_2436_);
                    v___x_2440_ = v___x_2421_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2441_, 1, v___x_2438_);
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
    mut v_tz_2444_: *mut crate::leanh::LeanObject,
    mut v_dt_2445_: *mut crate::leanh::LeanObject,
    mut v_hours_2446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2447_ = l_Std_Time_DateTime_subHours(v_tz_2444_, v_dt_2445_, v_hours_2446_);
    crate::leanh::lean_dec(v_hours_2446_);
    return v_res_2447_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addMinutes___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_2449_ = lean_nat_to_int(v___x_2448_);
    return v___x_2449_;
}
pub unsafe fn l_Std_Time_DateTime_addMinutes(
    mut v_tz_2450_: *mut crate::leanh::LeanObject,
    mut v_dt_2451_: *mut crate::leanh::LeanObject,
    mut v_minutes_2452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v_second_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut v_unused_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2453_ = crate::leanh::lean_ctor_get(v_dt_2451_, 0);
                v_isSharedCheck_2474_ = (!crate::leanh::lean_is_exclusive(v_dt_2451_)) as u8;
                if v_isSharedCheck_2474_ == 0 {
                    v_unused_2475_ = crate::leanh::lean_ctor_get(v_dt_2451_, 1);
                    crate::leanh::lean_dec(v_unused_2475_);
                    v___x_2455_ = v_dt_2451_;
                    v_isShared_2456_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2453_);
                    crate::leanh::lean_dec(v_dt_2451_);
                    v___x_2455_ = crate::leanh::lean_box(0);
                    v_isShared_2456_ = v_isSharedCheck_2474_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2457_ = crate::leanh::lean_ctor_get(v_timestamp_2453_, 0);
                crate::leanh::lean_inc(v_second_2457_);
                v_nano_2458_ = crate::leanh::lean_ctor_get(v_timestamp_2453_, 1);
                crate::leanh::lean_inc(v_nano_2458_);
                crate::leanh::lean_dec_ref(v_timestamp_2453_);
                v___x_2459_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_DateTime_addMinutes___closed__0,
                );
                v___x_2460_ = lean_int_mul(v_minutes_2452_, v___x_2459_);
                v___x_2461_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2462_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2463_ = lean_int_mul(v_second_2457_, v___x_2462_);
                crate::leanh::lean_dec(v_second_2457_);
                v___x_2464_ = lean_int_add(v___x_2463_, v_nano_2458_);
                crate::leanh::lean_dec(v_nano_2458_);
                crate::leanh::lean_dec(v___x_2463_);
                v___x_2465_ = lean_int_mul(v___x_2460_, v___x_2462_);
                crate::leanh::lean_dec(v___x_2460_);
                v___x_2466_ = lean_int_add(v___x_2465_, v___x_2461_);
                crate::leanh::lean_dec(v___x_2465_);
                v___x_2467_ = lean_int_add(v___x_2464_, v___x_2466_);
                crate::leanh::lean_dec(v___x_2466_);
                crate::leanh::lean_dec(v___x_2464_);
                v___x_2468_ = l_Std_Time_Duration_ofNanoseconds(v___x_2467_);
                crate::leanh::lean_dec(v___x_2467_);
                crate::leanh::lean_inc_ref(v___x_2468_);
                v___f_2469_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2469_, 0, v_tz_2450_);
                crate::leanh::lean_closure_set(v___f_2469_, 1, v___x_2468_);
                crate::leanh::lean_closure_set(v___f_2469_, 2, v___x_2462_);
                crate::leanh::lean_closure_set(v___f_2469_, 3, v___x_2461_);
                v___x_2470_ = lean_mk_thunk(v___f_2469_);
                if v_isShared_2456_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2455_, 1, v___x_2470_);
                    crate::leanh::lean_ctor_set(v___x_2455_, 0, v___x_2468_);
                    v___x_2472_ = v___x_2455_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 0, v___x_2468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 1, v___x_2470_);
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
    mut v_tz_2476_: *mut crate::leanh::LeanObject,
    mut v_dt_2477_: *mut crate::leanh::LeanObject,
    mut v_minutes_2478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2479_ = l_Std_Time_DateTime_addMinutes(v_tz_2476_, v_dt_2477_, v_minutes_2478_);
    crate::leanh::lean_dec(v_minutes_2478_);
    return v_res_2479_;
}
pub unsafe fn l_Std_Time_DateTime_subMinutes(
    mut v_tz_2480_: *mut crate::leanh::LeanObject,
    mut v_dt_2481_: *mut crate::leanh::LeanObject,
    mut v_minutes_2482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2486_: u8 = 0;
    let mut v_second_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2506_: u8 = 0;
    let mut v_unused_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2483_ = crate::leanh::lean_ctor_get(v_dt_2481_, 0);
                v_isSharedCheck_2506_ = (!crate::leanh::lean_is_exclusive(v_dt_2481_)) as u8;
                if v_isSharedCheck_2506_ == 0 {
                    v_unused_2507_ = crate::leanh::lean_ctor_get(v_dt_2481_, 1);
                    crate::leanh::lean_dec(v_unused_2507_);
                    v___x_2485_ = v_dt_2481_;
                    v_isShared_2486_ = v_isSharedCheck_2506_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2483_);
                    crate::leanh::lean_dec(v_dt_2481_);
                    v___x_2485_ = crate::leanh::lean_box(0);
                    v_isShared_2486_ = v_isSharedCheck_2506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2487_ = crate::leanh::lean_ctor_get(v_timestamp_2483_, 0);
                crate::leanh::lean_inc(v_second_2487_);
                v_nano_2488_ = crate::leanh::lean_ctor_get(v_timestamp_2483_, 1);
                crate::leanh::lean_inc(v_nano_2488_);
                crate::leanh::lean_dec_ref(v_timestamp_2483_);
                v___x_2489_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMinutes___closed__0_once),
                    _init_l_Std_Time_DateTime_addMinutes___closed__0,
                );
                v___x_2490_ = lean_int_mul(v_minutes_2482_, v___x_2489_);
                v___x_2491_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2492_ = lean_int_neg(v___x_2490_);
                crate::leanh::lean_dec(v___x_2490_);
                v___x_2493_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2494_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2495_ = lean_int_mul(v_second_2487_, v___x_2494_);
                crate::leanh::lean_dec(v_second_2487_);
                v___x_2496_ = lean_int_add(v___x_2495_, v_nano_2488_);
                crate::leanh::lean_dec(v_nano_2488_);
                crate::leanh::lean_dec(v___x_2495_);
                v___x_2497_ = lean_int_mul(v___x_2492_, v___x_2494_);
                crate::leanh::lean_dec(v___x_2492_);
                v___x_2498_ = lean_int_add(v___x_2497_, v___x_2493_);
                crate::leanh::lean_dec(v___x_2497_);
                v___x_2499_ = lean_int_add(v___x_2496_, v___x_2498_);
                crate::leanh::lean_dec(v___x_2498_);
                crate::leanh::lean_dec(v___x_2496_);
                v___x_2500_ = l_Std_Time_Duration_ofNanoseconds(v___x_2499_);
                crate::leanh::lean_dec(v___x_2499_);
                crate::leanh::lean_inc_ref(v___x_2500_);
                v___f_2501_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2501_, 0, v_tz_2480_);
                crate::leanh::lean_closure_set(v___f_2501_, 1, v___x_2500_);
                crate::leanh::lean_closure_set(v___f_2501_, 2, v___x_2494_);
                crate::leanh::lean_closure_set(v___f_2501_, 3, v___x_2491_);
                v___x_2502_ = lean_mk_thunk(v___f_2501_);
                if v_isShared_2486_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2485_, 1, v___x_2502_);
                    crate::leanh::lean_ctor_set(v___x_2485_, 0, v___x_2500_);
                    v___x_2504_ = v___x_2485_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2505_, 1, v___x_2502_);
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
    mut v_tz_2508_: *mut crate::leanh::LeanObject,
    mut v_dt_2509_: *mut crate::leanh::LeanObject,
    mut v_minutes_2510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2511_ = l_Std_Time_DateTime_subMinutes(v_tz_2508_, v_dt_2509_, v_minutes_2510_);
    crate::leanh::lean_dec(v_minutes_2510_);
    return v_res_2511_;
}
pub unsafe fn l_Std_Time_DateTime_addSeconds(
    mut v_tz_2512_: *mut crate::leanh::LeanObject,
    mut v_dt_2513_: *mut crate::leanh::LeanObject,
    mut v_seconds_2514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v_second_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_unused_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2515_ = crate::leanh::lean_ctor_get(v_dt_2513_, 0);
                v_isSharedCheck_2534_ = (!crate::leanh::lean_is_exclusive(v_dt_2513_)) as u8;
                if v_isSharedCheck_2534_ == 0 {
                    v_unused_2535_ = crate::leanh::lean_ctor_get(v_dt_2513_, 1);
                    crate::leanh::lean_dec(v_unused_2535_);
                    v___x_2517_ = v_dt_2513_;
                    v_isShared_2518_ = v_isSharedCheck_2534_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2515_);
                    crate::leanh::lean_dec(v_dt_2513_);
                    v___x_2517_ = crate::leanh::lean_box(0);
                    v_isShared_2518_ = v_isSharedCheck_2534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2519_ = crate::leanh::lean_ctor_get(v_timestamp_2515_, 0);
                crate::leanh::lean_inc(v_second_2519_);
                v_nano_2520_ = crate::leanh::lean_ctor_get(v_timestamp_2515_, 1);
                crate::leanh::lean_inc(v_nano_2520_);
                crate::leanh::lean_dec_ref(v_timestamp_2515_);
                v___x_2521_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2522_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2523_ = lean_int_mul(v_second_2519_, v___x_2522_);
                crate::leanh::lean_dec(v_second_2519_);
                v___x_2524_ = lean_int_add(v___x_2523_, v_nano_2520_);
                crate::leanh::lean_dec(v_nano_2520_);
                crate::leanh::lean_dec(v___x_2523_);
                v___x_2525_ = lean_int_mul(v_seconds_2514_, v___x_2522_);
                v___x_2526_ = lean_int_add(v___x_2525_, v___x_2521_);
                crate::leanh::lean_dec(v___x_2525_);
                v___x_2527_ = lean_int_add(v___x_2524_, v___x_2526_);
                crate::leanh::lean_dec(v___x_2526_);
                crate::leanh::lean_dec(v___x_2524_);
                v___x_2528_ = l_Std_Time_Duration_ofNanoseconds(v___x_2527_);
                crate::leanh::lean_dec(v___x_2527_);
                crate::leanh::lean_inc_ref(v___x_2528_);
                v___f_2529_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2529_, 0, v_tz_2512_);
                crate::leanh::lean_closure_set(v___f_2529_, 1, v___x_2528_);
                crate::leanh::lean_closure_set(v___f_2529_, 2, v___x_2522_);
                crate::leanh::lean_closure_set(v___f_2529_, 3, v___x_2521_);
                v___x_2530_ = lean_mk_thunk(v___f_2529_);
                if v_isShared_2518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2517_, 1, v___x_2530_);
                    crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2528_);
                    v___x_2532_ = v___x_2517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___x_2530_);
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
    mut v_tz_2536_: *mut crate::leanh::LeanObject,
    mut v_dt_2537_: *mut crate::leanh::LeanObject,
    mut v_seconds_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std_Time_DateTime_addSeconds(v_tz_2536_, v_dt_2537_, v_seconds_2538_);
    crate::leanh::lean_dec(v_seconds_2538_);
    return v_res_2539_;
}
pub unsafe fn l_Std_Time_DateTime_subSeconds(
    mut v_tz_2540_: *mut crate::leanh::LeanObject,
    mut v_dt_2541_: *mut crate::leanh::LeanObject,
    mut v_seconds_2542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2546_: u8 = 0;
    let mut v_second_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2543_ = crate::leanh::lean_ctor_get(v_dt_2541_, 0);
                v_isSharedCheck_2564_ = (!crate::leanh::lean_is_exclusive(v_dt_2541_)) as u8;
                if v_isSharedCheck_2564_ == 0 {
                    v_unused_2565_ = crate::leanh::lean_ctor_get(v_dt_2541_, 1);
                    crate::leanh::lean_dec(v_unused_2565_);
                    v___x_2545_ = v_dt_2541_;
                    v_isShared_2546_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2543_);
                    crate::leanh::lean_dec(v_dt_2541_);
                    v___x_2545_ = crate::leanh::lean_box(0);
                    v_isShared_2546_ = v_isSharedCheck_2564_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2547_ = crate::leanh::lean_ctor_get(v_timestamp_2543_, 0);
                crate::leanh::lean_inc(v_second_2547_);
                v_nano_2548_ = crate::leanh::lean_ctor_get(v_timestamp_2543_, 1);
                crate::leanh::lean_inc(v_nano_2548_);
                crate::leanh::lean_dec_ref(v_timestamp_2543_);
                v___x_2549_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2550_ = lean_int_neg(v_seconds_2542_);
                v___x_2551_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2552_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2553_ = lean_int_mul(v_second_2547_, v___x_2552_);
                crate::leanh::lean_dec(v_second_2547_);
                v___x_2554_ = lean_int_add(v___x_2553_, v_nano_2548_);
                crate::leanh::lean_dec(v_nano_2548_);
                crate::leanh::lean_dec(v___x_2553_);
                v___x_2555_ = lean_int_mul(v___x_2550_, v___x_2552_);
                crate::leanh::lean_dec(v___x_2550_);
                v___x_2556_ = lean_int_add(v___x_2555_, v___x_2551_);
                crate::leanh::lean_dec(v___x_2555_);
                v___x_2557_ = lean_int_add(v___x_2554_, v___x_2556_);
                crate::leanh::lean_dec(v___x_2556_);
                crate::leanh::lean_dec(v___x_2554_);
                v___x_2558_ = l_Std_Time_Duration_ofNanoseconds(v___x_2557_);
                crate::leanh::lean_dec(v___x_2557_);
                crate::leanh::lean_inc_ref(v___x_2558_);
                v___f_2559_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2559_, 0, v_tz_2540_);
                crate::leanh::lean_closure_set(v___f_2559_, 1, v___x_2558_);
                crate::leanh::lean_closure_set(v___f_2559_, 2, v___x_2552_);
                crate::leanh::lean_closure_set(v___f_2559_, 3, v___x_2549_);
                v___x_2560_ = lean_mk_thunk(v___f_2559_);
                if v_isShared_2546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2545_, 1, v___x_2560_);
                    crate::leanh::lean_ctor_set(v___x_2545_, 0, v___x_2558_);
                    v___x_2562_ = v___x_2545_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2563_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 0, v___x_2558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2563_, 1, v___x_2560_);
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
    mut v_tz_2566_: *mut crate::leanh::LeanObject,
    mut v_dt_2567_: *mut crate::leanh::LeanObject,
    mut v_seconds_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2569_ = l_Std_Time_DateTime_subSeconds(v_tz_2566_, v_dt_2567_, v_seconds_2568_);
    crate::leanh::lean_dec(v_seconds_2568_);
    return v_res_2569_;
}
pub unsafe fn l_Std_Time_DateTime_addMilliseconds___lam__0(
    mut v_tz_2570_: *mut crate::leanh::LeanObject,
    mut v___x_2571_: *mut crate::leanh::LeanObject,
    mut v___x_2572_: *mut crate::leanh::LeanObject,
    mut v_x_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_offset_2574_ = crate::leanh::lean_ctor_get(v_tz_2570_, 0);
    v_second_2575_ = crate::leanh::lean_ctor_get(v___x_2571_, 0);
    v_nano_2576_ = crate::leanh::lean_ctor_get(v___x_2571_, 1);
    v___x_2577_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
    );
    v___x_2578_ = lean_int_mul(v_second_2575_, v___x_2572_);
    v___x_2579_ = lean_int_add(v___x_2578_, v_nano_2576_);
    crate::leanh::lean_dec(v___x_2578_);
    v___x_2580_ = lean_int_mul(v_offset_2574_, v___x_2572_);
    v___x_2581_ = lean_int_add(v___x_2580_, v___x_2577_);
    crate::leanh::lean_dec(v___x_2580_);
    v___x_2582_ = lean_int_add(v___x_2579_, v___x_2581_);
    crate::leanh::lean_dec(v___x_2581_);
    crate::leanh::lean_dec(v___x_2579_);
    v___x_2583_ = l_Std_Time_Duration_ofNanoseconds(v___x_2582_);
    crate::leanh::lean_dec(v___x_2582_);
    v___x_2584_ = l_Std_Time_PlainDateTime_ofWallTime(v___x_2583_);
    return v___x_2584_;
}
pub unsafe fn l_Std_Time_DateTime_addMilliseconds___lam__0___boxed(
    mut v_tz_2585_: *mut crate::leanh::LeanObject,
    mut v___x_2586_: *mut crate::leanh::LeanObject,
    mut v___x_2587_: *mut crate::leanh::LeanObject,
    mut v_x_2588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2589_ = l_Std_Time_DateTime_addMilliseconds___lam__0(
        v_tz_2585_,
        v___x_2586_,
        v___x_2587_,
        v_x_2588_,
    );
    crate::leanh::lean_dec(v___x_2587_);
    crate::leanh::lean_dec_ref(v___x_2586_);
    crate::leanh::lean_dec_ref(v_tz_2585_);
    return v_res_2589_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2590_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_2591_ = lean_nat_to_int(v___x_2590_);
    return v___x_2591_;
}
pub unsafe fn l_Std_Time_DateTime_addMilliseconds(
    mut v_tz_2592_: *mut crate::leanh::LeanObject,
    mut v_dt_2593_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2598_: u8 = 0;
    let mut v_second_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2618_: u8 = 0;
    let mut v_unused_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2595_ = crate::leanh::lean_ctor_get(v_dt_2593_, 0);
                v_isSharedCheck_2618_ = (!crate::leanh::lean_is_exclusive(v_dt_2593_)) as u8;
                if v_isSharedCheck_2618_ == 0 {
                    v_unused_2619_ = crate::leanh::lean_ctor_get(v_dt_2593_, 1);
                    crate::leanh::lean_dec(v_unused_2619_);
                    v___x_2597_ = v_dt_2593_;
                    v_isShared_2598_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2595_);
                    crate::leanh::lean_dec(v_dt_2593_);
                    v___x_2597_ = crate::leanh::lean_box(0);
                    v_isShared_2598_ = v_isSharedCheck_2618_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2599_ = crate::leanh::lean_ctor_get(v_timestamp_2595_, 0);
                crate::leanh::lean_inc(v_second_2599_);
                v_nano_2600_ = crate::leanh::lean_ctor_get(v_timestamp_2595_, 1);
                crate::leanh::lean_inc(v_nano_2600_);
                crate::leanh::lean_dec_ref(v_timestamp_2595_);
                v___x_2601_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_addMilliseconds___closed__0,
                );
                v___x_2602_ = lean_int_mul(v_milliseconds_2594_, v___x_2601_);
                v___x_2603_ = l_Std_Time_Duration_ofNanoseconds(v___x_2602_);
                crate::leanh::lean_dec(v___x_2602_);
                v_second_2604_ = crate::leanh::lean_ctor_get(v___x_2603_, 0);
                crate::leanh::lean_inc(v_second_2604_);
                v_nano_2605_ = crate::leanh::lean_ctor_get(v___x_2603_, 1);
                crate::leanh::lean_inc(v_nano_2605_);
                crate::leanh::lean_dec_ref(v___x_2603_);
                v___x_2606_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2607_ = lean_int_mul(v_second_2599_, v___x_2606_);
                crate::leanh::lean_dec(v_second_2599_);
                v___x_2608_ = lean_int_add(v___x_2607_, v_nano_2600_);
                crate::leanh::lean_dec(v_nano_2600_);
                crate::leanh::lean_dec(v___x_2607_);
                v___x_2609_ = lean_int_mul(v_second_2604_, v___x_2606_);
                crate::leanh::lean_dec(v_second_2604_);
                v___x_2610_ = lean_int_add(v___x_2609_, v_nano_2605_);
                crate::leanh::lean_dec(v_nano_2605_);
                crate::leanh::lean_dec(v___x_2609_);
                v___x_2611_ = lean_int_add(v___x_2608_, v___x_2610_);
                crate::leanh::lean_dec(v___x_2610_);
                crate::leanh::lean_dec(v___x_2608_);
                v___x_2612_ = l_Std_Time_Duration_ofNanoseconds(v___x_2611_);
                crate::leanh::lean_dec(v___x_2611_);
                crate::leanh::lean_inc_ref(v___x_2612_);
                v___f_2613_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2613_, 0, v_tz_2592_);
                crate::leanh::lean_closure_set(v___f_2613_, 1, v___x_2612_);
                crate::leanh::lean_closure_set(v___f_2613_, 2, v___x_2606_);
                v___x_2614_ = lean_mk_thunk(v___f_2613_);
                if v_isShared_2598_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2597_, 1, v___x_2614_);
                    crate::leanh::lean_ctor_set(v___x_2597_, 0, v___x_2612_);
                    v___x_2616_ = v___x_2597_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2617_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 0, v___x_2612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2614_);
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
    mut v_tz_2620_: *mut crate::leanh::LeanObject,
    mut v_dt_2621_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2623_ = l_Std_Time_DateTime_addMilliseconds(v_tz_2620_, v_dt_2621_, v_milliseconds_2622_);
    crate::leanh::lean_dec(v_milliseconds_2622_);
    return v_res_2623_;
}
pub unsafe fn l_Std_Time_DateTime_subMilliseconds(
    mut v_tz_2624_: *mut crate::leanh::LeanObject,
    mut v_dt_2625_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_unused_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2627_ = crate::leanh::lean_ctor_get(v_dt_2625_, 0);
                v_isSharedCheck_2652_ = (!crate::leanh::lean_is_exclusive(v_dt_2625_)) as u8;
                if v_isSharedCheck_2652_ == 0 {
                    v_unused_2653_ = crate::leanh::lean_ctor_get(v_dt_2625_, 1);
                    crate::leanh::lean_dec(v_unused_2653_);
                    v___x_2629_ = v_dt_2625_;
                    v_isShared_2630_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2627_);
                    crate::leanh::lean_dec(v_dt_2625_);
                    v___x_2629_ = crate::leanh::lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2631_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_addMilliseconds___closed__0,
                );
                v___x_2632_ = lean_int_mul(v_milliseconds_2626_, v___x_2631_);
                v___x_2633_ = l_Std_Time_Duration_ofNanoseconds(v___x_2632_);
                crate::leanh::lean_dec(v___x_2632_);
                v_second_2634_ = crate::leanh::lean_ctor_get(v___x_2633_, 0);
                crate::leanh::lean_inc(v_second_2634_);
                v_nano_2635_ = crate::leanh::lean_ctor_get(v___x_2633_, 1);
                crate::leanh::lean_inc(v_nano_2635_);
                crate::leanh::lean_dec_ref(v___x_2633_);
                v_second_2636_ = crate::leanh::lean_ctor_get(v_timestamp_2627_, 0);
                crate::leanh::lean_inc(v_second_2636_);
                v_nano_2637_ = crate::leanh::lean_ctor_get(v_timestamp_2627_, 1);
                crate::leanh::lean_inc(v_nano_2637_);
                crate::leanh::lean_dec_ref(v_timestamp_2627_);
                v___x_2638_ = lean_int_neg(v_second_2634_);
                crate::leanh::lean_dec(v_second_2634_);
                v___x_2639_ = lean_int_neg(v_nano_2635_);
                crate::leanh::lean_dec(v_nano_2635_);
                v___x_2640_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2641_ = lean_int_mul(v_second_2636_, v___x_2640_);
                crate::leanh::lean_dec(v_second_2636_);
                v___x_2642_ = lean_int_add(v___x_2641_, v_nano_2637_);
                crate::leanh::lean_dec(v_nano_2637_);
                crate::leanh::lean_dec(v___x_2641_);
                v___x_2643_ = lean_int_mul(v___x_2638_, v___x_2640_);
                crate::leanh::lean_dec(v___x_2638_);
                v___x_2644_ = lean_int_add(v___x_2643_, v___x_2639_);
                crate::leanh::lean_dec(v___x_2639_);
                crate::leanh::lean_dec(v___x_2643_);
                v___x_2645_ = lean_int_add(v___x_2642_, v___x_2644_);
                crate::leanh::lean_dec(v___x_2644_);
                crate::leanh::lean_dec(v___x_2642_);
                v___x_2646_ = l_Std_Time_Duration_ofNanoseconds(v___x_2645_);
                crate::leanh::lean_dec(v___x_2645_);
                crate::leanh::lean_inc_ref(v___x_2646_);
                v___f_2647_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2647_, 0, v_tz_2624_);
                crate::leanh::lean_closure_set(v___f_2647_, 1, v___x_2646_);
                crate::leanh::lean_closure_set(v___f_2647_, 2, v___x_2640_);
                v___x_2648_ = lean_mk_thunk(v___f_2647_);
                if v_isShared_2630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2629_, 1, v___x_2648_);
                    crate::leanh::lean_ctor_set(v___x_2629_, 0, v___x_2646_);
                    v___x_2650_ = v___x_2629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2651_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2648_);
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
    mut v_tz_2654_: *mut crate::leanh::LeanObject,
    mut v_dt_2655_: *mut crate::leanh::LeanObject,
    mut v_milliseconds_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Std_Time_DateTime_subMilliseconds(v_tz_2654_, v_dt_2655_, v_milliseconds_2656_);
    crate::leanh::lean_dec(v_milliseconds_2656_);
    return v_res_2657_;
}
pub unsafe fn l_Std_Time_DateTime_addNanoseconds(
    mut v_tz_2658_: *mut crate::leanh::LeanObject,
    mut v_dt_2659_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2664_: u8 = 0;
    let mut v_second_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2682_: u8 = 0;
    let mut v_unused_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2661_ = crate::leanh::lean_ctor_get(v_dt_2659_, 0);
                v_isSharedCheck_2682_ = (!crate::leanh::lean_is_exclusive(v_dt_2659_)) as u8;
                if v_isSharedCheck_2682_ == 0 {
                    v_unused_2683_ = crate::leanh::lean_ctor_get(v_dt_2659_, 1);
                    crate::leanh::lean_dec(v_unused_2683_);
                    v___x_2663_ = v_dt_2659_;
                    v_isShared_2664_ = v_isSharedCheck_2682_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2661_);
                    crate::leanh::lean_dec(v_dt_2659_);
                    v___x_2663_ = crate::leanh::lean_box(0);
                    v_isShared_2664_ = v_isSharedCheck_2682_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2665_ = crate::leanh::lean_ctor_get(v_timestamp_2661_, 0);
                crate::leanh::lean_inc(v_second_2665_);
                v_nano_2666_ = crate::leanh::lean_ctor_get(v_timestamp_2661_, 1);
                crate::leanh::lean_inc(v_nano_2666_);
                crate::leanh::lean_dec_ref(v_timestamp_2661_);
                v___x_2667_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_2660_);
                v_second_2668_ = crate::leanh::lean_ctor_get(v___x_2667_, 0);
                crate::leanh::lean_inc(v_second_2668_);
                v_nano_2669_ = crate::leanh::lean_ctor_get(v___x_2667_, 1);
                crate::leanh::lean_inc(v_nano_2669_);
                crate::leanh::lean_dec_ref(v___x_2667_);
                v___x_2670_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2671_ = lean_int_mul(v_second_2665_, v___x_2670_);
                crate::leanh::lean_dec(v_second_2665_);
                v___x_2672_ = lean_int_add(v___x_2671_, v_nano_2666_);
                crate::leanh::lean_dec(v_nano_2666_);
                crate::leanh::lean_dec(v___x_2671_);
                v___x_2673_ = lean_int_mul(v_second_2668_, v___x_2670_);
                crate::leanh::lean_dec(v_second_2668_);
                v___x_2674_ = lean_int_add(v___x_2673_, v_nano_2669_);
                crate::leanh::lean_dec(v_nano_2669_);
                crate::leanh::lean_dec(v___x_2673_);
                v___x_2675_ = lean_int_add(v___x_2672_, v___x_2674_);
                crate::leanh::lean_dec(v___x_2674_);
                crate::leanh::lean_dec(v___x_2672_);
                v___x_2676_ = l_Std_Time_Duration_ofNanoseconds(v___x_2675_);
                crate::leanh::lean_dec(v___x_2675_);
                crate::leanh::lean_inc_ref(v___x_2676_);
                v___f_2677_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2677_, 0, v_tz_2658_);
                crate::leanh::lean_closure_set(v___f_2677_, 1, v___x_2676_);
                crate::leanh::lean_closure_set(v___f_2677_, 2, v___x_2670_);
                v___x_2678_ = lean_mk_thunk(v___f_2677_);
                if v_isShared_2664_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2663_, 1, v___x_2678_);
                    crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2676_);
                    v___x_2680_ = v___x_2663_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2681_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2681_, 1, v___x_2678_);
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
    mut v_tz_2684_: *mut crate::leanh::LeanObject,
    mut v_dt_2685_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_2686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2687_ = l_Std_Time_DateTime_addNanoseconds(v_tz_2684_, v_dt_2685_, v_nanoseconds_2686_);
    crate::leanh::lean_dec(v_nanoseconds_2686_);
    return v_res_2687_;
}
pub unsafe fn l_Std_Time_DateTime_subNanoseconds(
    mut v_tz_2688_: *mut crate::leanh::LeanObject,
    mut v_dt_2689_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_unused_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2691_ = crate::leanh::lean_ctor_get(v_dt_2689_, 0);
                v_isSharedCheck_2714_ = (!crate::leanh::lean_is_exclusive(v_dt_2689_)) as u8;
                if v_isSharedCheck_2714_ == 0 {
                    v_unused_2715_ = crate::leanh::lean_ctor_get(v_dt_2689_, 1);
                    crate::leanh::lean_dec(v_unused_2715_);
                    v___x_2693_ = v_dt_2689_;
                    v_isShared_2694_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2691_);
                    crate::leanh::lean_dec(v_dt_2689_);
                    v___x_2693_ = crate::leanh::lean_box(0);
                    v_isShared_2694_ = v_isSharedCheck_2714_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2695_ = l_Std_Time_Duration_ofNanoseconds(v_nanoseconds_2690_);
                v_second_2696_ = crate::leanh::lean_ctor_get(v___x_2695_, 0);
                crate::leanh::lean_inc(v_second_2696_);
                v_nano_2697_ = crate::leanh::lean_ctor_get(v___x_2695_, 1);
                crate::leanh::lean_inc(v_nano_2697_);
                crate::leanh::lean_dec_ref(v___x_2695_);
                v_second_2698_ = crate::leanh::lean_ctor_get(v_timestamp_2691_, 0);
                crate::leanh::lean_inc(v_second_2698_);
                v_nano_2699_ = crate::leanh::lean_ctor_get(v_timestamp_2691_, 1);
                crate::leanh::lean_inc(v_nano_2699_);
                crate::leanh::lean_dec_ref(v_timestamp_2691_);
                v___x_2700_ = lean_int_neg(v_second_2696_);
                crate::leanh::lean_dec(v_second_2696_);
                v___x_2701_ = lean_int_neg(v_nano_2697_);
                crate::leanh::lean_dec(v_nano_2697_);
                v___x_2702_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2703_ = lean_int_mul(v_second_2698_, v___x_2702_);
                crate::leanh::lean_dec(v_second_2698_);
                v___x_2704_ = lean_int_add(v___x_2703_, v_nano_2699_);
                crate::leanh::lean_dec(v_nano_2699_);
                crate::leanh::lean_dec(v___x_2703_);
                v___x_2705_ = lean_int_mul(v___x_2700_, v___x_2702_);
                crate::leanh::lean_dec(v___x_2700_);
                v___x_2706_ = lean_int_add(v___x_2705_, v___x_2701_);
                crate::leanh::lean_dec(v___x_2701_);
                crate::leanh::lean_dec(v___x_2705_);
                v___x_2707_ = lean_int_add(v___x_2704_, v___x_2706_);
                crate::leanh::lean_dec(v___x_2706_);
                crate::leanh::lean_dec(v___x_2704_);
                v___x_2708_ = l_Std_Time_Duration_ofNanoseconds(v___x_2707_);
                crate::leanh::lean_dec(v___x_2707_);
                crate::leanh::lean_inc_ref(v___x_2708_);
                v___f_2709_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2709_, 0, v_tz_2688_);
                crate::leanh::lean_closure_set(v___f_2709_, 1, v___x_2708_);
                crate::leanh::lean_closure_set(v___f_2709_, 2, v___x_2702_);
                v___x_2710_ = lean_mk_thunk(v___f_2709_);
                if v_isShared_2694_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2693_, 1, v___x_2710_);
                    crate::leanh::lean_ctor_set(v___x_2693_, 0, v___x_2708_);
                    v___x_2712_ = v___x_2693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 1, v___x_2710_);
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
    mut v_tz_2716_: *mut crate::leanh::LeanObject,
    mut v_dt_2717_: *mut crate::leanh::LeanObject,
    mut v_nanoseconds_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Std_Time_DateTime_subNanoseconds(v_tz_2716_, v_dt_2717_, v_nanoseconds_2718_);
    crate::leanh::lean_dec(v_nanoseconds_2718_);
    return v_res_2719_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addDays___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2720_ = crate::leanh::lean_unsigned_to_nat(86400);
    v___x_2721_ = lean_nat_to_int(v___x_2720_);
    return v___x_2721_;
}
pub unsafe fn l_Std_Time_DateTime_addDays(
    mut v_tz_2722_: *mut crate::leanh::LeanObject,
    mut v_dt_2723_: *mut crate::leanh::LeanObject,
    mut v_days_2724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2728_: u8 = 0;
    let mut v_second_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_unused_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2725_ = crate::leanh::lean_ctor_get(v_dt_2723_, 0);
                v_isSharedCheck_2746_ = (!crate::leanh::lean_is_exclusive(v_dt_2723_)) as u8;
                if v_isSharedCheck_2746_ == 0 {
                    v_unused_2747_ = crate::leanh::lean_ctor_get(v_dt_2723_, 1);
                    crate::leanh::lean_dec(v_unused_2747_);
                    v___x_2727_ = v_dt_2723_;
                    v_isShared_2728_ = v_isSharedCheck_2746_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2725_);
                    crate::leanh::lean_dec(v_dt_2723_);
                    v___x_2727_ = crate::leanh::lean_box(0);
                    v_isShared_2728_ = v_isSharedCheck_2746_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2729_ = crate::leanh::lean_ctor_get(v_timestamp_2725_, 0);
                crate::leanh::lean_inc(v_second_2729_);
                v_nano_2730_ = crate::leanh::lean_ctor_get(v_timestamp_2725_, 1);
                crate::leanh::lean_inc(v_nano_2730_);
                crate::leanh::lean_dec_ref(v_timestamp_2725_);
                v___x_2731_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2732_ = lean_int_mul(v_days_2724_, v___x_2731_);
                v___x_2733_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2734_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2735_ = lean_int_mul(v_second_2729_, v___x_2734_);
                crate::leanh::lean_dec(v_second_2729_);
                v___x_2736_ = lean_int_add(v___x_2735_, v_nano_2730_);
                crate::leanh::lean_dec(v_nano_2730_);
                crate::leanh::lean_dec(v___x_2735_);
                v___x_2737_ = lean_int_mul(v___x_2732_, v___x_2734_);
                crate::leanh::lean_dec(v___x_2732_);
                v___x_2738_ = lean_int_add(v___x_2737_, v___x_2733_);
                crate::leanh::lean_dec(v___x_2737_);
                v___x_2739_ = lean_int_add(v___x_2736_, v___x_2738_);
                crate::leanh::lean_dec(v___x_2738_);
                crate::leanh::lean_dec(v___x_2736_);
                v___x_2740_ = l_Std_Time_Duration_ofNanoseconds(v___x_2739_);
                crate::leanh::lean_dec(v___x_2739_);
                crate::leanh::lean_inc_ref(v___x_2740_);
                v___f_2741_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2741_, 0, v_tz_2722_);
                crate::leanh::lean_closure_set(v___f_2741_, 1, v___x_2740_);
                crate::leanh::lean_closure_set(v___f_2741_, 2, v___x_2734_);
                crate::leanh::lean_closure_set(v___f_2741_, 3, v___x_2733_);
                v___x_2742_ = lean_mk_thunk(v___f_2741_);
                if v_isShared_2728_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2727_, 1, v___x_2742_);
                    crate::leanh::lean_ctor_set(v___x_2727_, 0, v___x_2740_);
                    v___x_2744_ = v___x_2727_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2742_);
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
    mut v_tz_2748_: *mut crate::leanh::LeanObject,
    mut v_dt_2749_: *mut crate::leanh::LeanObject,
    mut v_days_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2751_ = l_Std_Time_DateTime_addDays(v_tz_2748_, v_dt_2749_, v_days_2750_);
    crate::leanh::lean_dec(v_days_2750_);
    return v_res_2751_;
}
pub unsafe fn l_Std_Time_DateTime_subDays(
    mut v_tz_2752_: *mut crate::leanh::LeanObject,
    mut v_dt_2753_: *mut crate::leanh::LeanObject,
    mut v_days_2754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v_second_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2778_: u8 = 0;
    let mut v_unused_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2755_ = crate::leanh::lean_ctor_get(v_dt_2753_, 0);
                v_isSharedCheck_2778_ = (!crate::leanh::lean_is_exclusive(v_dt_2753_)) as u8;
                if v_isSharedCheck_2778_ == 0 {
                    v_unused_2779_ = crate::leanh::lean_ctor_get(v_dt_2753_, 1);
                    crate::leanh::lean_dec(v_unused_2779_);
                    v___x_2757_ = v_dt_2753_;
                    v_isShared_2758_ = v_isSharedCheck_2778_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2755_);
                    crate::leanh::lean_dec(v_dt_2753_);
                    v___x_2757_ = crate::leanh::lean_box(0);
                    v_isShared_2758_ = v_isSharedCheck_2778_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2759_ = crate::leanh::lean_ctor_get(v_timestamp_2755_, 0);
                crate::leanh::lean_inc(v_second_2759_);
                v_nano_2760_ = crate::leanh::lean_ctor_get(v_timestamp_2755_, 1);
                crate::leanh::lean_inc(v_nano_2760_);
                crate::leanh::lean_dec_ref(v_timestamp_2755_);
                v___x_2761_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2762_ = lean_int_mul(v_days_2754_, v___x_2761_);
                v___x_2763_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2764_ = lean_int_neg(v___x_2762_);
                crate::leanh::lean_dec(v___x_2762_);
                v___x_2765_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2766_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2767_ = lean_int_mul(v_second_2759_, v___x_2766_);
                crate::leanh::lean_dec(v_second_2759_);
                v___x_2768_ = lean_int_add(v___x_2767_, v_nano_2760_);
                crate::leanh::lean_dec(v_nano_2760_);
                crate::leanh::lean_dec(v___x_2767_);
                v___x_2769_ = lean_int_mul(v___x_2764_, v___x_2766_);
                crate::leanh::lean_dec(v___x_2764_);
                v___x_2770_ = lean_int_add(v___x_2769_, v___x_2765_);
                crate::leanh::lean_dec(v___x_2769_);
                v___x_2771_ = lean_int_add(v___x_2768_, v___x_2770_);
                crate::leanh::lean_dec(v___x_2770_);
                crate::leanh::lean_dec(v___x_2768_);
                v___x_2772_ = l_Std_Time_Duration_ofNanoseconds(v___x_2771_);
                crate::leanh::lean_dec(v___x_2771_);
                crate::leanh::lean_inc_ref(v___x_2772_);
                v___f_2773_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2773_, 0, v_tz_2752_);
                crate::leanh::lean_closure_set(v___f_2773_, 1, v___x_2772_);
                crate::leanh::lean_closure_set(v___f_2773_, 2, v___x_2766_);
                crate::leanh::lean_closure_set(v___f_2773_, 3, v___x_2763_);
                v___x_2774_ = lean_mk_thunk(v___f_2773_);
                if v_isShared_2758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2757_, 1, v___x_2774_);
                    crate::leanh::lean_ctor_set(v___x_2757_, 0, v___x_2772_);
                    v___x_2776_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2777_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
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
    mut v_tz_2780_: *mut crate::leanh::LeanObject,
    mut v_dt_2781_: *mut crate::leanh::LeanObject,
    mut v_days_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2783_ = l_Std_Time_DateTime_subDays(v_tz_2780_, v_dt_2781_, v_days_2782_);
    crate::leanh::lean_dec(v_days_2782_);
    return v_res_2783_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addWeeks___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2784_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_2785_ = lean_nat_to_int(v___x_2784_);
    return v___x_2785_;
}
pub unsafe fn l_Std_Time_DateTime_addWeeks(
    mut v_tz_2786_: *mut crate::leanh::LeanObject,
    mut v_dt_2787_: *mut crate::leanh::LeanObject,
    mut v_weeks_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v_second_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2812_: u8 = 0;
    let mut v_unused_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2789_ = crate::leanh::lean_ctor_get(v_dt_2787_, 0);
                v_isSharedCheck_2812_ = (!crate::leanh::lean_is_exclusive(v_dt_2787_)) as u8;
                if v_isSharedCheck_2812_ == 0 {
                    v_unused_2813_ = crate::leanh::lean_ctor_get(v_dt_2787_, 1);
                    crate::leanh::lean_dec(v_unused_2813_);
                    v___x_2791_ = v_dt_2787_;
                    v_isShared_2792_ = v_isSharedCheck_2812_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2789_);
                    crate::leanh::lean_dec(v_dt_2787_);
                    v___x_2791_ = crate::leanh::lean_box(0);
                    v_isShared_2792_ = v_isSharedCheck_2812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2793_ = crate::leanh::lean_ctor_get(v_timestamp_2789_, 0);
                crate::leanh::lean_inc(v_second_2793_);
                v_nano_2794_ = crate::leanh::lean_ctor_get(v_timestamp_2789_, 1);
                crate::leanh::lean_inc(v_nano_2794_);
                crate::leanh::lean_dec_ref(v_timestamp_2789_);
                v___x_2795_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_DateTime_addWeeks___closed__0,
                );
                v___x_2796_ = lean_int_mul(v_weeks_2788_, v___x_2795_);
                v___x_2797_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2798_ = lean_int_mul(v___x_2796_, v___x_2797_);
                crate::leanh::lean_dec(v___x_2796_);
                v___x_2799_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2800_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2801_ = lean_int_mul(v_second_2793_, v___x_2800_);
                crate::leanh::lean_dec(v_second_2793_);
                v___x_2802_ = lean_int_add(v___x_2801_, v_nano_2794_);
                crate::leanh::lean_dec(v_nano_2794_);
                crate::leanh::lean_dec(v___x_2801_);
                v___x_2803_ = lean_int_mul(v___x_2798_, v___x_2800_);
                crate::leanh::lean_dec(v___x_2798_);
                v___x_2804_ = lean_int_add(v___x_2803_, v___x_2799_);
                crate::leanh::lean_dec(v___x_2803_);
                v___x_2805_ = lean_int_add(v___x_2802_, v___x_2804_);
                crate::leanh::lean_dec(v___x_2804_);
                crate::leanh::lean_dec(v___x_2802_);
                v___x_2806_ = l_Std_Time_Duration_ofNanoseconds(v___x_2805_);
                crate::leanh::lean_dec(v___x_2805_);
                crate::leanh::lean_inc_ref(v___x_2806_);
                v___f_2807_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2807_, 0, v_tz_2786_);
                crate::leanh::lean_closure_set(v___f_2807_, 1, v___x_2806_);
                crate::leanh::lean_closure_set(v___f_2807_, 2, v___x_2800_);
                crate::leanh::lean_closure_set(v___f_2807_, 3, v___x_2799_);
                v___x_2808_ = lean_mk_thunk(v___f_2807_);
                if v_isShared_2792_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2791_, 1, v___x_2808_);
                    crate::leanh::lean_ctor_set(v___x_2791_, 0, v___x_2806_);
                    v___x_2810_ = v___x_2791_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2811_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2811_, 1, v___x_2808_);
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
    mut v_tz_2814_: *mut crate::leanh::LeanObject,
    mut v_dt_2815_: *mut crate::leanh::LeanObject,
    mut v_weeks_2816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2817_ = l_Std_Time_DateTime_addWeeks(v_tz_2814_, v_dt_2815_, v_weeks_2816_);
    crate::leanh::lean_dec(v_weeks_2816_);
    return v_res_2817_;
}
pub unsafe fn l_Std_Time_DateTime_subWeeks(
    mut v_tz_2818_: *mut crate::leanh::LeanObject,
    mut v_dt_2819_: *mut crate::leanh::LeanObject,
    mut v_weeks_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v_second_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v_unused_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_2821_ = crate::leanh::lean_ctor_get(v_dt_2819_, 0);
                v_isSharedCheck_2846_ = (!crate::leanh::lean_is_exclusive(v_dt_2819_)) as u8;
                if v_isSharedCheck_2846_ == 0 {
                    v_unused_2847_ = crate::leanh::lean_ctor_get(v_dt_2819_, 1);
                    crate::leanh::lean_dec(v_unused_2847_);
                    v___x_2823_ = v_dt_2819_;
                    v_isShared_2824_ = v_isSharedCheck_2846_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_2821_);
                    crate::leanh::lean_dec(v_dt_2819_);
                    v___x_2823_ = crate::leanh::lean_box(0);
                    v_isShared_2824_ = v_isSharedCheck_2846_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_2825_ = crate::leanh::lean_ctor_get(v_timestamp_2821_, 0);
                crate::leanh::lean_inc(v_second_2825_);
                v_nano_2826_ = crate::leanh::lean_ctor_get(v_timestamp_2821_, 1);
                crate::leanh::lean_inc(v_nano_2826_);
                crate::leanh::lean_dec_ref(v_timestamp_2821_);
                v___x_2827_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addWeeks___closed__0_once),
                    _init_l_Std_Time_DateTime_addWeeks___closed__0,
                );
                v___x_2828_ = lean_int_mul(v_weeks_2820_, v___x_2827_);
                v___x_2829_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addDays___closed__0_once),
                    _init_l_Std_Time_DateTime_addDays___closed__0,
                );
                v___x_2830_ = lean_int_mul(v___x_2828_, v___x_2829_);
                crate::leanh::lean_dec(v___x_2828_);
                v___x_2831_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_2832_ = lean_int_neg(v___x_2830_);
                crate::leanh::lean_dec(v___x_2830_);
                v___x_2833_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2834_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2835_ = lean_int_mul(v_second_2825_, v___x_2834_);
                crate::leanh::lean_dec(v_second_2825_);
                v___x_2836_ = lean_int_add(v___x_2835_, v_nano_2826_);
                crate::leanh::lean_dec(v_nano_2826_);
                crate::leanh::lean_dec(v___x_2835_);
                v___x_2837_ = lean_int_mul(v___x_2832_, v___x_2834_);
                crate::leanh::lean_dec(v___x_2832_);
                v___x_2838_ = lean_int_add(v___x_2837_, v___x_2833_);
                crate::leanh::lean_dec(v___x_2837_);
                v___x_2839_ = lean_int_add(v___x_2836_, v___x_2838_);
                crate::leanh::lean_dec(v___x_2838_);
                crate::leanh::lean_dec(v___x_2836_);
                v___x_2840_ = l_Std_Time_Duration_ofNanoseconds(v___x_2839_);
                crate::leanh::lean_dec(v___x_2839_);
                crate::leanh::lean_inc_ref(v___x_2840_);
                v___f_2841_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addHours___lam__0___boxed as *mut core::ffi::c_void,
                    5,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_2841_, 0, v_tz_2818_);
                crate::leanh::lean_closure_set(v___f_2841_, 1, v___x_2840_);
                crate::leanh::lean_closure_set(v___f_2841_, 2, v___x_2834_);
                crate::leanh::lean_closure_set(v___f_2841_, 3, v___x_2831_);
                v___x_2842_ = lean_mk_thunk(v___f_2841_);
                if v_isShared_2824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2823_, 1, v___x_2842_);
                    crate::leanh::lean_ctor_set(v___x_2823_, 0, v___x_2840_);
                    v___x_2844_ = v___x_2823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2845_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2842_);
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
    mut v_tz_2848_: *mut crate::leanh::LeanObject,
    mut v_dt_2849_: *mut crate::leanh::LeanObject,
    mut v_weeks_2850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2851_ = l_Std_Time_DateTime_subWeeks(v_tz_2848_, v_dt_2849_, v_weeks_2850_);
    crate::leanh::lean_dec(v_weeks_2850_);
    return v_res_2851_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsClip___lam__0(
    mut v___x_2852_: *mut crate::leanh::LeanObject,
    mut v_x_2853_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___x_2852_);
    return v___x_2852_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsClip___lam__0___boxed(
    mut v___x_2854_: *mut crate::leanh::LeanObject,
    mut v_x_2855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2856_ = l_Std_Time_DateTime_addMonthsClip___lam__0(v___x_2854_, v_x_2855_);
    crate::leanh::lean_dec_ref(v___x_2854_);
    return v_res_2856_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsClip(
    mut v_tz_2857_: *mut crate::leanh::LeanObject,
    mut v_dt_2858_: *mut crate::leanh::LeanObject,
    mut v_months_2859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v_offset_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2884_: u8 = 0;
    let mut v_unused_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2860_ = crate::leanh::lean_ctor_get(v_dt_2858_, 1);
                v_isSharedCheck_2884_ = (!crate::leanh::lean_is_exclusive(v_dt_2858_)) as u8;
                if v_isSharedCheck_2884_ == 0 {
                    v_unused_2885_ = crate::leanh::lean_ctor_get(v_dt_2858_, 0);
                    crate::leanh::lean_dec(v_unused_2885_);
                    v___x_2862_ = v_dt_2858_;
                    v_isShared_2863_ = v_isSharedCheck_2884_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_2860_);
                    crate::leanh::lean_dec(v_dt_2858_);
                    v___x_2862_ = crate::leanh::lean_box(0);
                    v_isShared_2863_ = v_isSharedCheck_2884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_offset_2864_ = crate::leanh::lean_ctor_get(v_tz_2857_, 0);
                v___x_2865_ = lean_thunk_get_own(v_date_2860_);
                crate::leanh::lean_dec_ref(v_date_2860_);
                v___x_2866_ = l_Std_Time_PlainDateTime_addMonthsClip(v___x_2865_, v_months_2859_);
                crate::leanh::lean_inc_ref(v___x_2866_);
                v___x_2867_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2866_);
                v_second_2868_ = crate::leanh::lean_ctor_get(v___x_2867_, 0);
                crate::leanh::lean_inc(v_second_2868_);
                v_nano_2869_ = crate::leanh::lean_ctor_get(v___x_2867_, 1);
                crate::leanh::lean_inc(v_nano_2869_);
                crate::leanh::lean_dec_ref(v___x_2867_);
                v___f_2870_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2870_, 0, v___x_2866_);
                v___x_2871_ = lean_int_neg(v_offset_2864_);
                v___x_2872_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2873_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2874_ = lean_int_mul(v_second_2868_, v___x_2873_);
                crate::leanh::lean_dec(v_second_2868_);
                v___x_2875_ = lean_int_add(v___x_2874_, v_nano_2869_);
                crate::leanh::lean_dec(v_nano_2869_);
                crate::leanh::lean_dec(v___x_2874_);
                v___x_2876_ = lean_int_mul(v___x_2871_, v___x_2873_);
                crate::leanh::lean_dec(v___x_2871_);
                v___x_2877_ = lean_int_add(v___x_2876_, v___x_2872_);
                crate::leanh::lean_dec(v___x_2876_);
                v___x_2878_ = lean_int_add(v___x_2875_, v___x_2877_);
                crate::leanh::lean_dec(v___x_2877_);
                crate::leanh::lean_dec(v___x_2875_);
                v_tm_2879_ = l_Std_Time_Duration_ofNanoseconds(v___x_2878_);
                crate::leanh::lean_dec(v___x_2878_);
                v___x_2880_ = lean_mk_thunk(v___f_2870_);
                if v_isShared_2863_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2862_, 1, v___x_2880_);
                    crate::leanh::lean_ctor_set(v___x_2862_, 0, v_tm_2879_);
                    v___x_2882_ = v___x_2862_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_tm_2879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2880_);
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
    mut v_tz_2886_: *mut crate::leanh::LeanObject,
    mut v_dt_2887_: *mut crate::leanh::LeanObject,
    mut v_months_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2889_ = l_Std_Time_DateTime_addMonthsClip(v_tz_2886_, v_dt_2887_, v_months_2888_);
    crate::leanh::lean_dec(v_months_2888_);
    crate::leanh::lean_dec_ref(v_tz_2886_);
    return v_res_2889_;
}
pub unsafe fn l_Std_Time_DateTime_subMonthsClip(
    mut v_tz_2890_: *mut crate::leanh::LeanObject,
    mut v_dt_2891_: *mut crate::leanh::LeanObject,
    mut v_months_2892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2902_: u8 = 0;
    let mut v_offset_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_isSharedCheck_2927_: u8 = 0;
    let mut v_unused_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2893_ = crate::leanh::lean_ctor_get(v_dt_2891_, 1);
                v_isSharedCheck_2927_ = (!crate::leanh::lean_is_exclusive(v_dt_2891_)) as u8;
                if v_isSharedCheck_2927_ == 0 {
                    v_unused_2928_ = crate::leanh::lean_ctor_get(v_dt_2891_, 0);
                    crate::leanh::lean_dec(v_unused_2928_);
                    v___x_2895_ = v_dt_2891_;
                    v_isShared_2896_ = v_isSharedCheck_2927_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_2893_);
                    crate::leanh::lean_dec(v_dt_2891_);
                    v___x_2895_ = crate::leanh::lean_box(0);
                    v_isShared_2896_ = v_isSharedCheck_2927_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2897_ = lean_thunk_get_own(v_date_2893_);
                crate::leanh::lean_dec_ref(v_date_2893_);
                v_date_2898_ = crate::leanh::lean_ctor_get(v___x_2897_, 0);
                v_time_2899_ = crate::leanh::lean_ctor_get(v___x_2897_, 1);
                v_isSharedCheck_2926_ = (!crate::leanh::lean_is_exclusive(v___x_2897_)) as u8;
                if v_isSharedCheck_2926_ == 0 {
                    v___x_2901_ = v___x_2897_;
                    v_isShared_2902_ = v_isSharedCheck_2926_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2899_);
                    crate::leanh::lean_inc(v_date_2898_);
                    crate::leanh::lean_dec(v___x_2897_);
                    v___x_2901_ = crate::leanh::lean_box(0);
                    v_isShared_2902_ = v_isSharedCheck_2926_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_2903_ = crate::leanh::lean_ctor_get(v_tz_2890_, 0);
                v___x_2904_ = lean_int_neg(v_months_2892_);
                v___x_2905_ = l_Std_Time_PlainDate_addMonthsClip(v_date_2898_, v___x_2904_);
                crate::leanh::lean_dec(v___x_2904_);
                if v_isShared_2902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2901_, 0, v___x_2905_);
                    v___x_2907_ = v___x_2901_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_time_2899_);
                    v___x_2907_ = v_reuseFailAlloc_2925_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2907_);
                v___x_2908_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2907_);
                v_second_2909_ = crate::leanh::lean_ctor_get(v___x_2908_, 0);
                crate::leanh::lean_inc(v_second_2909_);
                v_nano_2910_ = crate::leanh::lean_ctor_get(v___x_2908_, 1);
                crate::leanh::lean_inc(v_nano_2910_);
                crate::leanh::lean_dec_ref(v___x_2908_);
                v___f_2911_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2911_, 0, v___x_2907_);
                v___x_2912_ = lean_int_neg(v_offset_2903_);
                v___x_2913_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2914_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2915_ = lean_int_mul(v_second_2909_, v___x_2914_);
                crate::leanh::lean_dec(v_second_2909_);
                v___x_2916_ = lean_int_add(v___x_2915_, v_nano_2910_);
                crate::leanh::lean_dec(v_nano_2910_);
                crate::leanh::lean_dec(v___x_2915_);
                v___x_2917_ = lean_int_mul(v___x_2912_, v___x_2914_);
                crate::leanh::lean_dec(v___x_2912_);
                v___x_2918_ = lean_int_add(v___x_2917_, v___x_2913_);
                crate::leanh::lean_dec(v___x_2917_);
                v___x_2919_ = lean_int_add(v___x_2916_, v___x_2918_);
                crate::leanh::lean_dec(v___x_2918_);
                crate::leanh::lean_dec(v___x_2916_);
                v_tm_2920_ = l_Std_Time_Duration_ofNanoseconds(v___x_2919_);
                crate::leanh::lean_dec(v___x_2919_);
                v___x_2921_ = lean_mk_thunk(v___f_2911_);
                if v_isShared_2896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2895_, 1, v___x_2921_);
                    crate::leanh::lean_ctor_set(v___x_2895_, 0, v_tm_2920_);
                    v___x_2923_ = v___x_2895_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2924_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_tm_2920_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2924_, 1, v___x_2921_);
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
    mut v_tz_2929_: *mut crate::leanh::LeanObject,
    mut v_dt_2930_: *mut crate::leanh::LeanObject,
    mut v_months_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Std_Time_DateTime_subMonthsClip(v_tz_2929_, v_dt_2930_, v_months_2931_);
    crate::leanh::lean_dec(v_months_2931_);
    crate::leanh::lean_dec_ref(v_tz_2929_);
    return v_res_2932_;
}
pub unsafe fn l_Std_Time_DateTime_addMonthsRollOver(
    mut v_tz_2933_: *mut crate::leanh::LeanObject,
    mut v_dt_2934_: *mut crate::leanh::LeanObject,
    mut v_months_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v_offset_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2960_: u8 = 0;
    let mut v_unused_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2936_ = crate::leanh::lean_ctor_get(v_dt_2934_, 1);
                v_isSharedCheck_2960_ = (!crate::leanh::lean_is_exclusive(v_dt_2934_)) as u8;
                if v_isSharedCheck_2960_ == 0 {
                    v_unused_2961_ = crate::leanh::lean_ctor_get(v_dt_2934_, 0);
                    crate::leanh::lean_dec(v_unused_2961_);
                    v___x_2938_ = v_dt_2934_;
                    v_isShared_2939_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_2936_);
                    crate::leanh::lean_dec(v_dt_2934_);
                    v___x_2938_ = crate::leanh::lean_box(0);
                    v_isShared_2939_ = v_isSharedCheck_2960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_offset_2940_ = crate::leanh::lean_ctor_get(v_tz_2933_, 0);
                v___x_2941_ = lean_thunk_get_own(v_date_2936_);
                crate::leanh::lean_dec_ref(v_date_2936_);
                v___x_2942_ =
                    l_Std_Time_PlainDateTime_addMonthsRollOver(v___x_2941_, v_months_2935_);
                crate::leanh::lean_inc_ref(v___x_2942_);
                v___x_2943_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2942_);
                v_second_2944_ = crate::leanh::lean_ctor_get(v___x_2943_, 0);
                crate::leanh::lean_inc(v_second_2944_);
                v_nano_2945_ = crate::leanh::lean_ctor_get(v___x_2943_, 1);
                crate::leanh::lean_inc(v_nano_2945_);
                crate::leanh::lean_dec_ref(v___x_2943_);
                v___f_2946_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2946_, 0, v___x_2942_);
                v___x_2947_ = lean_int_neg(v_offset_2940_);
                v___x_2948_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2949_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2950_ = lean_int_mul(v_second_2944_, v___x_2949_);
                crate::leanh::lean_dec(v_second_2944_);
                v___x_2951_ = lean_int_add(v___x_2950_, v_nano_2945_);
                crate::leanh::lean_dec(v_nano_2945_);
                crate::leanh::lean_dec(v___x_2950_);
                v___x_2952_ = lean_int_mul(v___x_2947_, v___x_2949_);
                crate::leanh::lean_dec(v___x_2947_);
                v___x_2953_ = lean_int_add(v___x_2952_, v___x_2948_);
                crate::leanh::lean_dec(v___x_2952_);
                v___x_2954_ = lean_int_add(v___x_2951_, v___x_2953_);
                crate::leanh::lean_dec(v___x_2953_);
                crate::leanh::lean_dec(v___x_2951_);
                v_tm_2955_ = l_Std_Time_Duration_ofNanoseconds(v___x_2954_);
                crate::leanh::lean_dec(v___x_2954_);
                v___x_2956_ = lean_mk_thunk(v___f_2946_);
                if v_isShared_2939_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2938_, 1, v___x_2956_);
                    crate::leanh::lean_ctor_set(v___x_2938_, 0, v_tm_2955_);
                    v___x_2958_ = v___x_2938_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_tm_2955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2959_, 1, v___x_2956_);
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
    mut v_tz_2962_: *mut crate::leanh::LeanObject,
    mut v_dt_2963_: *mut crate::leanh::LeanObject,
    mut v_months_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2965_ = l_Std_Time_DateTime_addMonthsRollOver(v_tz_2962_, v_dt_2963_, v_months_2964_);
    crate::leanh::lean_dec(v_months_2964_);
    crate::leanh::lean_dec_ref(v_tz_2962_);
    return v_res_2965_;
}
pub unsafe fn l_Std_Time_DateTime_subMonthsRollOver(
    mut v_tz_2966_: *mut crate::leanh::LeanObject,
    mut v_dt_2967_: *mut crate::leanh::LeanObject,
    mut v_months_2968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v_offset_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_isSharedCheck_3003_: u8 = 0;
    let mut v_unused_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_2969_ = crate::leanh::lean_ctor_get(v_dt_2967_, 1);
                v_isSharedCheck_3003_ = (!crate::leanh::lean_is_exclusive(v_dt_2967_)) as u8;
                if v_isSharedCheck_3003_ == 0 {
                    v_unused_3004_ = crate::leanh::lean_ctor_get(v_dt_2967_, 0);
                    crate::leanh::lean_dec(v_unused_3004_);
                    v___x_2971_ = v_dt_2967_;
                    v_isShared_2972_ = v_isSharedCheck_3003_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_2969_);
                    crate::leanh::lean_dec(v_dt_2967_);
                    v___x_2971_ = crate::leanh::lean_box(0);
                    v_isShared_2972_ = v_isSharedCheck_3003_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2973_ = lean_thunk_get_own(v_date_2969_);
                crate::leanh::lean_dec_ref(v_date_2969_);
                v_date_2974_ = crate::leanh::lean_ctor_get(v___x_2973_, 0);
                v_time_2975_ = crate::leanh::lean_ctor_get(v___x_2973_, 1);
                v_isSharedCheck_3002_ = (!crate::leanh::lean_is_exclusive(v___x_2973_)) as u8;
                if v_isSharedCheck_3002_ == 0 {
                    v___x_2977_ = v___x_2973_;
                    v_isShared_2978_ = v_isSharedCheck_3002_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_2975_);
                    crate::leanh::lean_inc(v_date_2974_);
                    crate::leanh::lean_dec(v___x_2973_);
                    v___x_2977_ = crate::leanh::lean_box(0);
                    v_isShared_2978_ = v_isSharedCheck_3002_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_2979_ = crate::leanh::lean_ctor_get(v_tz_2966_, 0);
                v___x_2980_ = lean_int_neg(v_months_2968_);
                v___x_2981_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_2974_, v___x_2980_);
                crate::leanh::lean_dec(v___x_2980_);
                if v_isShared_2978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2977_, 0, v___x_2981_);
                    v___x_2983_ = v___x_2977_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_time_2975_);
                    v___x_2983_ = v_reuseFailAlloc_3001_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_2983_);
                v___x_2984_ = l_Std_Time_PlainDateTime_toWallTime(v___x_2983_);
                v_second_2985_ = crate::leanh::lean_ctor_get(v___x_2984_, 0);
                crate::leanh::lean_inc(v_second_2985_);
                v_nano_2986_ = crate::leanh::lean_ctor_get(v___x_2984_, 1);
                crate::leanh::lean_inc(v_nano_2986_);
                crate::leanh::lean_dec_ref(v___x_2984_);
                v___f_2987_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2987_, 0, v___x_2983_);
                v___x_2988_ = lean_int_neg(v_offset_2979_);
                v___x_2989_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_2990_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_2991_ = lean_int_mul(v_second_2985_, v___x_2990_);
                crate::leanh::lean_dec(v_second_2985_);
                v___x_2992_ = lean_int_add(v___x_2991_, v_nano_2986_);
                crate::leanh::lean_dec(v_nano_2986_);
                crate::leanh::lean_dec(v___x_2991_);
                v___x_2993_ = lean_int_mul(v___x_2988_, v___x_2990_);
                crate::leanh::lean_dec(v___x_2988_);
                v___x_2994_ = lean_int_add(v___x_2993_, v___x_2989_);
                crate::leanh::lean_dec(v___x_2993_);
                v___x_2995_ = lean_int_add(v___x_2992_, v___x_2994_);
                crate::leanh::lean_dec(v___x_2994_);
                crate::leanh::lean_dec(v___x_2992_);
                v_tm_2996_ = l_Std_Time_Duration_ofNanoseconds(v___x_2995_);
                crate::leanh::lean_dec(v___x_2995_);
                v___x_2997_ = lean_mk_thunk(v___f_2987_);
                if v_isShared_2972_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2971_, 1, v___x_2997_);
                    crate::leanh::lean_ctor_set(v___x_2971_, 0, v_tm_2996_);
                    v___x_2999_ = v___x_2971_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3000_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_tm_2996_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3000_, 1, v___x_2997_);
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
    mut v_tz_3005_: *mut crate::leanh::LeanObject,
    mut v_dt_3006_: *mut crate::leanh::LeanObject,
    mut v_months_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3008_ = l_Std_Time_DateTime_subMonthsRollOver(v_tz_3005_, v_dt_3006_, v_months_3007_);
    crate::leanh::lean_dec(v_months_3007_);
    crate::leanh::lean_dec_ref(v_tz_3005_);
    return v_res_3008_;
}
pub unsafe fn _init_l_Std_Time_DateTime_addYearsRollOver___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3009_ = crate::leanh::lean_unsigned_to_nat(12);
    v___x_3010_ = lean_nat_to_int(v___x_3009_);
    return v___x_3010_;
}
pub unsafe fn l_Std_Time_DateTime_addYearsRollOver(
    mut v_tz_3011_: *mut crate::leanh::LeanObject,
    mut v_dt_3012_: *mut crate::leanh::LeanObject,
    mut v_years_3013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3023_: u8 = 0;
    let mut v_offset_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_isSharedCheck_3049_: u8 = 0;
    let mut v_unused_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3014_ = crate::leanh::lean_ctor_get(v_dt_3012_, 1);
                v_isSharedCheck_3049_ = (!crate::leanh::lean_is_exclusive(v_dt_3012_)) as u8;
                if v_isSharedCheck_3049_ == 0 {
                    v_unused_3050_ = crate::leanh::lean_ctor_get(v_dt_3012_, 0);
                    crate::leanh::lean_dec(v_unused_3050_);
                    v___x_3016_ = v_dt_3012_;
                    v_isShared_3017_ = v_isSharedCheck_3049_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3014_);
                    crate::leanh::lean_dec(v_dt_3012_);
                    v___x_3016_ = crate::leanh::lean_box(0);
                    v_isShared_3017_ = v_isSharedCheck_3049_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3018_ = lean_thunk_get_own(v_date_3014_);
                crate::leanh::lean_dec_ref(v_date_3014_);
                v_date_3019_ = crate::leanh::lean_ctor_get(v___x_3018_, 0);
                v_time_3020_ = crate::leanh::lean_ctor_get(v___x_3018_, 1);
                v_isSharedCheck_3048_ = (!crate::leanh::lean_is_exclusive(v___x_3018_)) as u8;
                if v_isSharedCheck_3048_ == 0 {
                    v___x_3022_ = v___x_3018_;
                    v_isShared_3023_ = v_isSharedCheck_3048_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3020_);
                    crate::leanh::lean_inc(v_date_3019_);
                    crate::leanh::lean_dec(v___x_3018_);
                    v___x_3022_ = crate::leanh::lean_box(0);
                    v_isShared_3023_ = v_isSharedCheck_3048_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3024_ = crate::leanh::lean_ctor_get(v_tz_3011_, 0);
                v___x_3025_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3026_ = lean_int_mul(v_years_3013_, v___x_3025_);
                v___x_3027_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_3019_, v___x_3026_);
                crate::leanh::lean_dec(v___x_3026_);
                if v_isShared_3023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3022_, 0, v___x_3027_);
                    v___x_3029_ = v___x_3022_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3047_, 1, v_time_3020_);
                    v___x_3029_ = v_reuseFailAlloc_3047_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3029_);
                v___x_3030_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3029_);
                v_second_3031_ = crate::leanh::lean_ctor_get(v___x_3030_, 0);
                crate::leanh::lean_inc(v_second_3031_);
                v_nano_3032_ = crate::leanh::lean_ctor_get(v___x_3030_, 1);
                crate::leanh::lean_inc(v_nano_3032_);
                crate::leanh::lean_dec_ref(v___x_3030_);
                v___f_3033_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3033_, 0, v___x_3029_);
                v___x_3034_ = lean_int_neg(v_offset_3024_);
                v___x_3035_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3036_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3037_ = lean_int_mul(v_second_3031_, v___x_3036_);
                crate::leanh::lean_dec(v_second_3031_);
                v___x_3038_ = lean_int_add(v___x_3037_, v_nano_3032_);
                crate::leanh::lean_dec(v_nano_3032_);
                crate::leanh::lean_dec(v___x_3037_);
                v___x_3039_ = lean_int_mul(v___x_3034_, v___x_3036_);
                crate::leanh::lean_dec(v___x_3034_);
                v___x_3040_ = lean_int_add(v___x_3039_, v___x_3035_);
                crate::leanh::lean_dec(v___x_3039_);
                v___x_3041_ = lean_int_add(v___x_3038_, v___x_3040_);
                crate::leanh::lean_dec(v___x_3040_);
                crate::leanh::lean_dec(v___x_3038_);
                v_tm_3042_ = l_Std_Time_Duration_ofNanoseconds(v___x_3041_);
                crate::leanh::lean_dec(v___x_3041_);
                v___x_3043_ = lean_mk_thunk(v___f_3033_);
                if v_isShared_3017_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3016_, 1, v___x_3043_);
                    crate::leanh::lean_ctor_set(v___x_3016_, 0, v_tm_3042_);
                    v___x_3045_ = v___x_3016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_tm_3042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3043_);
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
    mut v_tz_3051_: *mut crate::leanh::LeanObject,
    mut v_dt_3052_: *mut crate::leanh::LeanObject,
    mut v_years_3053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3054_ = l_Std_Time_DateTime_addYearsRollOver(v_tz_3051_, v_dt_3052_, v_years_3053_);
    crate::leanh::lean_dec(v_years_3053_);
    crate::leanh::lean_dec_ref(v_tz_3051_);
    return v_res_3054_;
}
pub unsafe fn l_Std_Time_DateTime_addYearsClip(
    mut v_tz_3055_: *mut crate::leanh::LeanObject,
    mut v_dt_3056_: *mut crate::leanh::LeanObject,
    mut v_years_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3061_: u8 = 0;
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v_offset_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut v_isSharedCheck_3093_: u8 = 0;
    let mut v_unused_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3058_ = crate::leanh::lean_ctor_get(v_dt_3056_, 1);
                v_isSharedCheck_3093_ = (!crate::leanh::lean_is_exclusive(v_dt_3056_)) as u8;
                if v_isSharedCheck_3093_ == 0 {
                    v_unused_3094_ = crate::leanh::lean_ctor_get(v_dt_3056_, 0);
                    crate::leanh::lean_dec(v_unused_3094_);
                    v___x_3060_ = v_dt_3056_;
                    v_isShared_3061_ = v_isSharedCheck_3093_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3058_);
                    crate::leanh::lean_dec(v_dt_3056_);
                    v___x_3060_ = crate::leanh::lean_box(0);
                    v_isShared_3061_ = v_isSharedCheck_3093_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3062_ = lean_thunk_get_own(v_date_3058_);
                crate::leanh::lean_dec_ref(v_date_3058_);
                v_date_3063_ = crate::leanh::lean_ctor_get(v___x_3062_, 0);
                v_time_3064_ = crate::leanh::lean_ctor_get(v___x_3062_, 1);
                v_isSharedCheck_3092_ = (!crate::leanh::lean_is_exclusive(v___x_3062_)) as u8;
                if v_isSharedCheck_3092_ == 0 {
                    v___x_3066_ = v___x_3062_;
                    v_isShared_3067_ = v_isSharedCheck_3092_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3064_);
                    crate::leanh::lean_inc(v_date_3063_);
                    crate::leanh::lean_dec(v___x_3062_);
                    v___x_3066_ = crate::leanh::lean_box(0);
                    v_isShared_3067_ = v_isSharedCheck_3092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3068_ = crate::leanh::lean_ctor_get(v_tz_3055_, 0);
                v___x_3069_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3070_ = lean_int_mul(v_years_3057_, v___x_3069_);
                v___x_3071_ = l_Std_Time_PlainDate_addMonthsClip(v_date_3063_, v___x_3070_);
                crate::leanh::lean_dec(v___x_3070_);
                if v_isShared_3067_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3066_, 0, v___x_3071_);
                    v___x_3073_ = v___x_3066_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3091_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3091_, 1, v_time_3064_);
                    v___x_3073_ = v_reuseFailAlloc_3091_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3073_);
                v___x_3074_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3073_);
                v_second_3075_ = crate::leanh::lean_ctor_get(v___x_3074_, 0);
                crate::leanh::lean_inc(v_second_3075_);
                v_nano_3076_ = crate::leanh::lean_ctor_get(v___x_3074_, 1);
                crate::leanh::lean_inc(v_nano_3076_);
                crate::leanh::lean_dec_ref(v___x_3074_);
                v___f_3077_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3077_, 0, v___x_3073_);
                v___x_3078_ = lean_int_neg(v_offset_3068_);
                v___x_3079_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3080_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3081_ = lean_int_mul(v_second_3075_, v___x_3080_);
                crate::leanh::lean_dec(v_second_3075_);
                v___x_3082_ = lean_int_add(v___x_3081_, v_nano_3076_);
                crate::leanh::lean_dec(v_nano_3076_);
                crate::leanh::lean_dec(v___x_3081_);
                v___x_3083_ = lean_int_mul(v___x_3078_, v___x_3080_);
                crate::leanh::lean_dec(v___x_3078_);
                v___x_3084_ = lean_int_add(v___x_3083_, v___x_3079_);
                crate::leanh::lean_dec(v___x_3083_);
                v___x_3085_ = lean_int_add(v___x_3082_, v___x_3084_);
                crate::leanh::lean_dec(v___x_3084_);
                crate::leanh::lean_dec(v___x_3082_);
                v_tm_3086_ = l_Std_Time_Duration_ofNanoseconds(v___x_3085_);
                crate::leanh::lean_dec(v___x_3085_);
                v___x_3087_ = lean_mk_thunk(v___f_3077_);
                if v_isShared_3061_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3060_, 1, v___x_3087_);
                    crate::leanh::lean_ctor_set(v___x_3060_, 0, v_tm_3086_);
                    v___x_3089_ = v___x_3060_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_tm_3086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3090_, 1, v___x_3087_);
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
    mut v_tz_3095_: *mut crate::leanh::LeanObject,
    mut v_dt_3096_: *mut crate::leanh::LeanObject,
    mut v_years_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3098_ = l_Std_Time_DateTime_addYearsClip(v_tz_3095_, v_dt_3096_, v_years_3097_);
    crate::leanh::lean_dec(v_years_3097_);
    crate::leanh::lean_dec_ref(v_tz_3095_);
    return v_res_3098_;
}
pub unsafe fn l_Std_Time_DateTime_subYearsRollOver(
    mut v_tz_3099_: *mut crate::leanh::LeanObject,
    mut v_dt_3100_: *mut crate::leanh::LeanObject,
    mut v_years_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3111_: u8 = 0;
    let mut v_offset_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_isSharedCheck_3138_: u8 = 0;
    let mut v_unused_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3102_ = crate::leanh::lean_ctor_get(v_dt_3100_, 1);
                v_isSharedCheck_3138_ = (!crate::leanh::lean_is_exclusive(v_dt_3100_)) as u8;
                if v_isSharedCheck_3138_ == 0 {
                    v_unused_3139_ = crate::leanh::lean_ctor_get(v_dt_3100_, 0);
                    crate::leanh::lean_dec(v_unused_3139_);
                    v___x_3104_ = v_dt_3100_;
                    v_isShared_3105_ = v_isSharedCheck_3138_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3102_);
                    crate::leanh::lean_dec(v_dt_3100_);
                    v___x_3104_ = crate::leanh::lean_box(0);
                    v_isShared_3105_ = v_isSharedCheck_3138_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3106_ = lean_thunk_get_own(v_date_3102_);
                crate::leanh::lean_dec_ref(v_date_3102_);
                v_date_3107_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                v_time_3108_ = crate::leanh::lean_ctor_get(v___x_3106_, 1);
                v_isSharedCheck_3137_ = (!crate::leanh::lean_is_exclusive(v___x_3106_)) as u8;
                if v_isSharedCheck_3137_ == 0 {
                    v___x_3110_ = v___x_3106_;
                    v_isShared_3111_ = v_isSharedCheck_3137_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3108_);
                    crate::leanh::lean_inc(v_date_3107_);
                    crate::leanh::lean_dec(v___x_3106_);
                    v___x_3110_ = crate::leanh::lean_box(0);
                    v_isShared_3111_ = v_isSharedCheck_3137_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3112_ = crate::leanh::lean_ctor_get(v_tz_3099_, 0);
                v___x_3113_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3114_ = lean_int_mul(v_years_3101_, v___x_3113_);
                v___x_3115_ = lean_int_neg(v___x_3114_);
                crate::leanh::lean_dec(v___x_3114_);
                v___x_3116_ = l_Std_Time_PlainDate_addMonthsRollOver(v_date_3107_, v___x_3115_);
                crate::leanh::lean_dec(v___x_3115_);
                if v_isShared_3111_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3110_, 0, v___x_3116_);
                    v___x_3118_ = v___x_3110_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_time_3108_);
                    v___x_3118_ = v_reuseFailAlloc_3136_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3118_);
                v___x_3119_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3118_);
                v_second_3120_ = crate::leanh::lean_ctor_get(v___x_3119_, 0);
                crate::leanh::lean_inc(v_second_3120_);
                v_nano_3121_ = crate::leanh::lean_ctor_get(v___x_3119_, 1);
                crate::leanh::lean_inc(v_nano_3121_);
                crate::leanh::lean_dec_ref(v___x_3119_);
                v___f_3122_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3122_, 0, v___x_3118_);
                v___x_3123_ = lean_int_neg(v_offset_3112_);
                v___x_3124_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3125_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3126_ = lean_int_mul(v_second_3120_, v___x_3125_);
                crate::leanh::lean_dec(v_second_3120_);
                v___x_3127_ = lean_int_add(v___x_3126_, v_nano_3121_);
                crate::leanh::lean_dec(v_nano_3121_);
                crate::leanh::lean_dec(v___x_3126_);
                v___x_3128_ = lean_int_mul(v___x_3123_, v___x_3125_);
                crate::leanh::lean_dec(v___x_3123_);
                v___x_3129_ = lean_int_add(v___x_3128_, v___x_3124_);
                crate::leanh::lean_dec(v___x_3128_);
                v___x_3130_ = lean_int_add(v___x_3127_, v___x_3129_);
                crate::leanh::lean_dec(v___x_3129_);
                crate::leanh::lean_dec(v___x_3127_);
                v_tm_3131_ = l_Std_Time_Duration_ofNanoseconds(v___x_3130_);
                crate::leanh::lean_dec(v___x_3130_);
                v___x_3132_ = lean_mk_thunk(v___f_3122_);
                if v_isShared_3105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3104_, 1, v___x_3132_);
                    crate::leanh::lean_ctor_set(v___x_3104_, 0, v_tm_3131_);
                    v___x_3134_ = v___x_3104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_tm_3131_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 1, v___x_3132_);
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
    mut v_tz_3140_: *mut crate::leanh::LeanObject,
    mut v_dt_3141_: *mut crate::leanh::LeanObject,
    mut v_years_3142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3143_ = l_Std_Time_DateTime_subYearsRollOver(v_tz_3140_, v_dt_3141_, v_years_3142_);
    crate::leanh::lean_dec(v_years_3142_);
    crate::leanh::lean_dec_ref(v_tz_3140_);
    return v_res_3143_;
}
pub unsafe fn l_Std_Time_DateTime_subYearsClip(
    mut v_tz_3144_: *mut crate::leanh::LeanObject,
    mut v_dt_3145_: *mut crate::leanh::LeanObject,
    mut v_years_3146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3150_: u8 = 0;
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v_offset_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3182_: u8 = 0;
    let mut v_isSharedCheck_3183_: u8 = 0;
    let mut v_unused_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3147_ = crate::leanh::lean_ctor_get(v_dt_3145_, 1);
                v_isSharedCheck_3183_ = (!crate::leanh::lean_is_exclusive(v_dt_3145_)) as u8;
                if v_isSharedCheck_3183_ == 0 {
                    v_unused_3184_ = crate::leanh::lean_ctor_get(v_dt_3145_, 0);
                    crate::leanh::lean_dec(v_unused_3184_);
                    v___x_3149_ = v_dt_3145_;
                    v_isShared_3150_ = v_isSharedCheck_3183_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3147_);
                    crate::leanh::lean_dec(v_dt_3145_);
                    v___x_3149_ = crate::leanh::lean_box(0);
                    v_isShared_3150_ = v_isSharedCheck_3183_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3151_ = lean_thunk_get_own(v_date_3147_);
                crate::leanh::lean_dec_ref(v_date_3147_);
                v_date_3152_ = crate::leanh::lean_ctor_get(v___x_3151_, 0);
                v_time_3153_ = crate::leanh::lean_ctor_get(v___x_3151_, 1);
                v_isSharedCheck_3182_ = (!crate::leanh::lean_is_exclusive(v___x_3151_)) as u8;
                if v_isSharedCheck_3182_ == 0 {
                    v___x_3155_ = v___x_3151_;
                    v_isShared_3156_ = v_isSharedCheck_3182_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3153_);
                    crate::leanh::lean_inc(v_date_3152_);
                    crate::leanh::lean_dec(v___x_3151_);
                    v___x_3155_ = crate::leanh::lean_box(0);
                    v_isShared_3156_ = v_isSharedCheck_3182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_offset_3157_ = crate::leanh::lean_ctor_get(v_tz_3144_, 0);
                v___x_3158_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addYearsRollOver___closed__0_once),
                    _init_l_Std_Time_DateTime_addYearsRollOver___closed__0,
                );
                v___x_3159_ = lean_int_mul(v_years_3146_, v___x_3158_);
                v___x_3160_ = lean_int_neg(v___x_3159_);
                crate::leanh::lean_dec(v___x_3159_);
                v___x_3161_ = l_Std_Time_PlainDate_addMonthsClip(v_date_3152_, v___x_3160_);
                crate::leanh::lean_dec(v___x_3160_);
                if v_isShared_3156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3155_, 0, v___x_3161_);
                    v___x_3163_ = v___x_3155_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3181_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 0, v___x_3161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3181_, 1, v_time_3153_);
                    v___x_3163_ = v_reuseFailAlloc_3181_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3163_);
                v___x_3164_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3163_);
                v_second_3165_ = crate::leanh::lean_ctor_get(v___x_3164_, 0);
                crate::leanh::lean_inc(v_second_3165_);
                v_nano_3166_ = crate::leanh::lean_ctor_get(v___x_3164_, 1);
                crate::leanh::lean_inc(v_nano_3166_);
                crate::leanh::lean_dec_ref(v___x_3164_);
                v___f_3167_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3167_, 0, v___x_3163_);
                v___x_3168_ = lean_int_neg(v_offset_3157_);
                v___x_3169_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3170_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3171_ = lean_int_mul(v_second_3165_, v___x_3170_);
                crate::leanh::lean_dec(v_second_3165_);
                v___x_3172_ = lean_int_add(v___x_3171_, v_nano_3166_);
                crate::leanh::lean_dec(v_nano_3166_);
                crate::leanh::lean_dec(v___x_3171_);
                v___x_3173_ = lean_int_mul(v___x_3168_, v___x_3170_);
                crate::leanh::lean_dec(v___x_3168_);
                v___x_3174_ = lean_int_add(v___x_3173_, v___x_3169_);
                crate::leanh::lean_dec(v___x_3173_);
                v___x_3175_ = lean_int_add(v___x_3172_, v___x_3174_);
                crate::leanh::lean_dec(v___x_3174_);
                crate::leanh::lean_dec(v___x_3172_);
                v_tm_3176_ = l_Std_Time_Duration_ofNanoseconds(v___x_3175_);
                crate::leanh::lean_dec(v___x_3175_);
                v___x_3177_ = lean_mk_thunk(v___f_3167_);
                if v_isShared_3150_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3149_, 1, v___x_3177_);
                    crate::leanh::lean_ctor_set(v___x_3149_, 0, v_tm_3176_);
                    v___x_3179_ = v___x_3149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_tm_3176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 1, v___x_3177_);
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
    mut v_tz_3185_: *mut crate::leanh::LeanObject,
    mut v_dt_3186_: *mut crate::leanh::LeanObject,
    mut v_years_3187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3188_ = l_Std_Time_DateTime_subYearsClip(v_tz_3185_, v_dt_3186_, v_years_3187_);
    crate::leanh::lean_dec(v_years_3187_);
    crate::leanh::lean_dec_ref(v_tz_3185_);
    return v_res_3188_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withDaysClip___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3189_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3190_ = lean_nat_to_int(v___x_3189_);
    return v___x_3190_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withDaysClip___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3191_ = crate::leanh::lean_unsigned_to_nat(400);
    v___x_3192_ = lean_nat_to_int(v___x_3191_);
    return v___x_3192_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withDaysClip___closed__2() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3193_ = crate::leanh::lean_unsigned_to_nat(100);
    v___x_3194_ = lean_nat_to_int(v___x_3193_);
    return v___x_3194_;
}
pub unsafe fn l_Std_Time_DateTime_withDaysClip(
    mut v_tz_3195_: *mut crate::leanh::LeanObject,
    mut v_dt_3196_: *mut crate::leanh::LeanObject,
    mut v_days_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3208_: u8 = 0;
    let mut v_offset_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v_unused_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___y_3239_: u8 = 0;
    let mut v_max_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: u8 = 0;
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v_isSharedCheck_3259_: u8 = 0;
    let mut v_unused_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3261_: u8 = 0;
    let mut v_unused_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3198_ = crate::leanh::lean_ctor_get(v_dt_3196_, 1);
                v_isSharedCheck_3261_ = (!crate::leanh::lean_is_exclusive(v_dt_3196_)) as u8;
                if v_isSharedCheck_3261_ == 0 {
                    v_unused_3262_ = crate::leanh::lean_ctor_get(v_dt_3196_, 0);
                    crate::leanh::lean_dec(v_unused_3262_);
                    v___x_3200_ = v_dt_3196_;
                    v_isShared_3201_ = v_isSharedCheck_3261_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3198_);
                    crate::leanh::lean_dec(v_dt_3196_);
                    v___x_3200_ = crate::leanh::lean_box(0);
                    v_isShared_3201_ = v_isSharedCheck_3261_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3202_ = lean_thunk_get_own(v_date_3198_);
                crate::leanh::lean_dec_ref(v_date_3198_);
                v_date_3232_ = crate::leanh::lean_ctor_get(v___x_3202_, 0);
                crate::leanh::lean_inc_ref(v_date_3232_);
                v_year_3233_ = crate::leanh::lean_ctor_get(v_date_3232_, 0);
                v_month_3234_ = crate::leanh::lean_ctor_get(v_date_3232_, 1);
                v_isSharedCheck_3259_ = (!crate::leanh::lean_is_exclusive(v_date_3232_)) as u8;
                if v_isSharedCheck_3259_ == 0 {
                    v_unused_3260_ = crate::leanh::lean_ctor_get(v_date_3232_, 2);
                    crate::leanh::lean_dec(v_unused_3260_);
                    v___x_3236_ = v_date_3232_;
                    v_isShared_3237_ = v_isSharedCheck_3259_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_month_3234_);
                    crate::leanh::lean_inc(v_year_3233_);
                    crate::leanh::lean_dec(v_date_3232_);
                    v___x_3236_ = crate::leanh::lean_box(0);
                    v_isShared_3237_ = v_isSharedCheck_3259_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3205_ = crate::leanh::lean_ctor_get(v___x_3202_, 1);
                v_isSharedCheck_3230_ = (!crate::leanh::lean_is_exclusive(v___x_3202_)) as u8;
                if v_isSharedCheck_3230_ == 0 {
                    v_unused_3231_ = crate::leanh::lean_ctor_get(v___x_3202_, 0);
                    crate::leanh::lean_dec(v_unused_3231_);
                    v___x_3207_ = v___x_3202_;
                    v_isShared_3208_ = v_isSharedCheck_3230_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3205_);
                    crate::leanh::lean_dec(v___x_3202_);
                    v___x_3207_ = crate::leanh::lean_box(0);
                    v_isShared_3208_ = v_isSharedCheck_3230_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3209_ = crate::leanh::lean_ctor_get(v_tz_3195_, 0);
                if v_isShared_3208_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3207_, 0, v___y_3204_);
                    v___x_3211_ = v___x_3207_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___y_3204_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 1, v_time_3205_);
                    v___x_3211_ = v_reuseFailAlloc_3229_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_3211_);
                v___x_3212_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3211_);
                v_second_3213_ = crate::leanh::lean_ctor_get(v___x_3212_, 0);
                crate::leanh::lean_inc(v_second_3213_);
                v_nano_3214_ = crate::leanh::lean_ctor_get(v___x_3212_, 1);
                crate::leanh::lean_inc(v_nano_3214_);
                crate::leanh::lean_dec_ref(v___x_3212_);
                v___f_3215_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3215_, 0, v___x_3211_);
                v___x_3216_ = lean_int_neg(v_offset_3209_);
                v___x_3217_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3218_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3219_ = lean_int_mul(v_second_3213_, v___x_3218_);
                crate::leanh::lean_dec(v_second_3213_);
                v___x_3220_ = lean_int_add(v___x_3219_, v_nano_3214_);
                crate::leanh::lean_dec(v_nano_3214_);
                crate::leanh::lean_dec(v___x_3219_);
                v___x_3221_ = lean_int_mul(v___x_3216_, v___x_3218_);
                crate::leanh::lean_dec(v___x_3216_);
                v___x_3222_ = lean_int_add(v___x_3221_, v___x_3217_);
                crate::leanh::lean_dec(v___x_3221_);
                v___x_3223_ = lean_int_add(v___x_3220_, v___x_3222_);
                crate::leanh::lean_dec(v___x_3222_);
                crate::leanh::lean_dec(v___x_3220_);
                v_tm_3224_ = l_Std_Time_Duration_ofNanoseconds(v___x_3223_);
                crate::leanh::lean_dec(v___x_3223_);
                v___x_3225_ = lean_mk_thunk(v___f_3215_);
                if v_isShared_3201_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3200_, 1, v___x_3225_);
                    crate::leanh::lean_ctor_set(v___x_3200_, 0, v_tm_3224_);
                    v___x_3227_ = v___x_3200_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3228_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3228_, 0, v_tm_3224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3228_, 1, v___x_3225_);
                    v___x_3227_ = v_reuseFailAlloc_3228_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3227_;
            }
            6 => {
                v___x_3248_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_3249_ = lean_int_mod(v_year_3233_, v___x_3248_);
                v___x_3250_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3255_ = lean_int_dec_eq(v___x_3249_, v___x_3250_);
                crate::leanh::lean_dec(v___x_3249_);
                if v___x_3255_ == 0 {
                    v___y_3239_ = v___x_3255_;
                    state = 7;
                    continue;
                } else {
                    v___x_3256_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_3257_ = lean_int_mod(v_year_3233_, v___x_3256_);
                    v___x_3258_ = lean_int_dec_eq(v___x_3257_, v___x_3250_);
                    crate::leanh::lean_dec(v___x_3257_);
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
                    crate::leanh::lean_dec(v_max_3240_);
                    if v_isShared_3237_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3236_, 2, v_days_3197_);
                        v___x_3243_ = v___x_3236_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3244_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_year_3233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 1, v_month_3234_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3244_, 2, v_days_3197_);
                        v___x_3243_ = v_reuseFailAlloc_3244_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_days_3197_);
                    if v_isShared_3237_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3236_, 2, v_max_3240_);
                        v___x_3246_ = v___x_3236_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_year_3233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 1, v_month_3234_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 2, v_max_3240_);
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
                v___x_3252_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_3253_ = lean_int_mod(v_year_3233_, v___x_3252_);
                v___x_3254_ = lean_int_dec_eq(v___x_3253_, v___x_3250_);
                crate::leanh::lean_dec(v___x_3253_);
                v___y_3239_ = v___x_3254_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withDaysClip___boxed(
    mut v_tz_3263_: *mut crate::leanh::LeanObject,
    mut v_dt_3264_: *mut crate::leanh::LeanObject,
    mut v_days_3265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3266_ = l_Std_Time_DateTime_withDaysClip(v_tz_3263_, v_dt_3264_, v_days_3265_);
    crate::leanh::lean_dec_ref(v_tz_3263_);
    return v_res_3266_;
}
pub unsafe fn l_Std_Time_DateTime_withDaysRollOver(
    mut v_tz_3267_: *mut crate::leanh::LeanObject,
    mut v_dt_3268_: *mut crate::leanh::LeanObject,
    mut v_days_3269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3273_: u8 = 0;
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v_year_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3304_: u8 = 0;
    let mut v_isSharedCheck_3305_: u8 = 0;
    let mut v_unused_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3270_ = crate::leanh::lean_ctor_get(v_dt_3268_, 1);
                v_isSharedCheck_3305_ = (!crate::leanh::lean_is_exclusive(v_dt_3268_)) as u8;
                if v_isSharedCheck_3305_ == 0 {
                    v_unused_3306_ = crate::leanh::lean_ctor_get(v_dt_3268_, 0);
                    crate::leanh::lean_dec(v_unused_3306_);
                    v___x_3272_ = v_dt_3268_;
                    v_isShared_3273_ = v_isSharedCheck_3305_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3270_);
                    crate::leanh::lean_dec(v_dt_3268_);
                    v___x_3272_ = crate::leanh::lean_box(0);
                    v_isShared_3273_ = v_isSharedCheck_3305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3274_ = lean_thunk_get_own(v_date_3270_);
                crate::leanh::lean_dec_ref(v_date_3270_);
                v_date_3275_ = crate::leanh::lean_ctor_get(v___x_3274_, 0);
                v_time_3276_ = crate::leanh::lean_ctor_get(v___x_3274_, 1);
                v_isSharedCheck_3304_ = (!crate::leanh::lean_is_exclusive(v___x_3274_)) as u8;
                if v_isSharedCheck_3304_ == 0 {
                    v___x_3278_ = v___x_3274_;
                    v_isShared_3279_ = v_isSharedCheck_3304_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3276_);
                    crate::leanh::lean_inc(v_date_3275_);
                    crate::leanh::lean_dec(v___x_3274_);
                    v___x_3278_ = crate::leanh::lean_box(0);
                    v_isShared_3279_ = v_isSharedCheck_3304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3280_ = crate::leanh::lean_ctor_get(v_date_3275_, 0);
                crate::leanh::lean_inc(v_year_3280_);
                v_month_3281_ = crate::leanh::lean_ctor_get(v_date_3275_, 1);
                crate::leanh::lean_inc(v_month_3281_);
                crate::leanh::lean_dec_ref(v_date_3275_);
                v_offset_3282_ = crate::leanh::lean_ctor_get(v_tz_3267_, 0);
                v___x_3283_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3280_, v_month_3281_, v_days_3269_);
                if v_isShared_3279_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3278_, 0, v___x_3283_);
                    v___x_3285_ = v___x_3278_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 0, v___x_3283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3303_, 1, v_time_3276_);
                    v___x_3285_ = v_reuseFailAlloc_3303_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3285_);
                v___x_3286_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3285_);
                v_second_3287_ = crate::leanh::lean_ctor_get(v___x_3286_, 0);
                crate::leanh::lean_inc(v_second_3287_);
                v_nano_3288_ = crate::leanh::lean_ctor_get(v___x_3286_, 1);
                crate::leanh::lean_inc(v_nano_3288_);
                crate::leanh::lean_dec_ref(v___x_3286_);
                v___f_3289_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3289_, 0, v___x_3285_);
                v___x_3290_ = lean_int_neg(v_offset_3282_);
                v___x_3291_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3292_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3293_ = lean_int_mul(v_second_3287_, v___x_3292_);
                crate::leanh::lean_dec(v_second_3287_);
                v___x_3294_ = lean_int_add(v___x_3293_, v_nano_3288_);
                crate::leanh::lean_dec(v_nano_3288_);
                crate::leanh::lean_dec(v___x_3293_);
                v___x_3295_ = lean_int_mul(v___x_3290_, v___x_3292_);
                crate::leanh::lean_dec(v___x_3290_);
                v___x_3296_ = lean_int_add(v___x_3295_, v___x_3291_);
                crate::leanh::lean_dec(v___x_3295_);
                v___x_3297_ = lean_int_add(v___x_3294_, v___x_3296_);
                crate::leanh::lean_dec(v___x_3296_);
                crate::leanh::lean_dec(v___x_3294_);
                v_tm_3298_ = l_Std_Time_Duration_ofNanoseconds(v___x_3297_);
                crate::leanh::lean_dec(v___x_3297_);
                v___x_3299_ = lean_mk_thunk(v___f_3289_);
                if v_isShared_3273_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3272_, 1, v___x_3299_);
                    crate::leanh::lean_ctor_set(v___x_3272_, 0, v_tm_3298_);
                    v___x_3301_ = v___x_3272_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3302_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_tm_3298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3302_, 1, v___x_3299_);
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
    mut v_tz_3307_: *mut crate::leanh::LeanObject,
    mut v_dt_3308_: *mut crate::leanh::LeanObject,
    mut v_days_3309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3310_ = l_Std_Time_DateTime_withDaysRollOver(v_tz_3307_, v_dt_3308_, v_days_3309_);
    crate::leanh::lean_dec(v_days_3309_);
    crate::leanh::lean_dec_ref(v_tz_3307_);
    return v_res_3310_;
}
pub unsafe fn l_Std_Time_DateTime_withMonthClip(
    mut v_tz_3311_: *mut crate::leanh::LeanObject,
    mut v_dt_3312_: *mut crate::leanh::LeanObject,
    mut v_month_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3324_: u8 = 0;
    let mut v_offset_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3353_: u8 = 0;
    let mut v___y_3355_: u8 = 0;
    let mut v_max_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: u8 = 0;
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: u8 = 0;
    let mut v___x_3371_: u8 = 0;
    let mut v___x_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: u8 = 0;
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut v_unused_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3377_: u8 = 0;
    let mut v_unused_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3314_ = crate::leanh::lean_ctor_get(v_dt_3312_, 1);
                v_isSharedCheck_3377_ = (!crate::leanh::lean_is_exclusive(v_dt_3312_)) as u8;
                if v_isSharedCheck_3377_ == 0 {
                    v_unused_3378_ = crate::leanh::lean_ctor_get(v_dt_3312_, 0);
                    crate::leanh::lean_dec(v_unused_3378_);
                    v___x_3316_ = v_dt_3312_;
                    v_isShared_3317_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3314_);
                    crate::leanh::lean_dec(v_dt_3312_);
                    v___x_3316_ = crate::leanh::lean_box(0);
                    v_isShared_3317_ = v_isSharedCheck_3377_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3318_ = lean_thunk_get_own(v_date_3314_);
                crate::leanh::lean_dec_ref(v_date_3314_);
                v_date_3348_ = crate::leanh::lean_ctor_get(v___x_3318_, 0);
                crate::leanh::lean_inc_ref(v_date_3348_);
                v_year_3349_ = crate::leanh::lean_ctor_get(v_date_3348_, 0);
                v_day_3350_ = crate::leanh::lean_ctor_get(v_date_3348_, 2);
                v_isSharedCheck_3375_ = (!crate::leanh::lean_is_exclusive(v_date_3348_)) as u8;
                if v_isSharedCheck_3375_ == 0 {
                    v_unused_3376_ = crate::leanh::lean_ctor_get(v_date_3348_, 1);
                    crate::leanh::lean_dec(v_unused_3376_);
                    v___x_3352_ = v_date_3348_;
                    v_isShared_3353_ = v_isSharedCheck_3375_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_3350_);
                    crate::leanh::lean_inc(v_year_3349_);
                    crate::leanh::lean_dec(v_date_3348_);
                    v___x_3352_ = crate::leanh::lean_box(0);
                    v_isShared_3353_ = v_isSharedCheck_3375_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3321_ = crate::leanh::lean_ctor_get(v___x_3318_, 1);
                v_isSharedCheck_3346_ = (!crate::leanh::lean_is_exclusive(v___x_3318_)) as u8;
                if v_isSharedCheck_3346_ == 0 {
                    v_unused_3347_ = crate::leanh::lean_ctor_get(v___x_3318_, 0);
                    crate::leanh::lean_dec(v_unused_3347_);
                    v___x_3323_ = v___x_3318_;
                    v_isShared_3324_ = v_isSharedCheck_3346_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3321_);
                    crate::leanh::lean_dec(v___x_3318_);
                    v___x_3323_ = crate::leanh::lean_box(0);
                    v_isShared_3324_ = v_isSharedCheck_3346_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3325_ = crate::leanh::lean_ctor_get(v_tz_3311_, 0);
                if v_isShared_3324_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3323_, 0, v___y_3320_);
                    v___x_3327_ = v___x_3323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___y_3320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3345_, 1, v_time_3321_);
                    v___x_3327_ = v_reuseFailAlloc_3345_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_3327_);
                v___x_3328_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3327_);
                v_second_3329_ = crate::leanh::lean_ctor_get(v___x_3328_, 0);
                crate::leanh::lean_inc(v_second_3329_);
                v_nano_3330_ = crate::leanh::lean_ctor_get(v___x_3328_, 1);
                crate::leanh::lean_inc(v_nano_3330_);
                crate::leanh::lean_dec_ref(v___x_3328_);
                v___f_3331_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3331_, 0, v___x_3327_);
                v___x_3332_ = lean_int_neg(v_offset_3325_);
                v___x_3333_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3334_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3335_ = lean_int_mul(v_second_3329_, v___x_3334_);
                crate::leanh::lean_dec(v_second_3329_);
                v___x_3336_ = lean_int_add(v___x_3335_, v_nano_3330_);
                crate::leanh::lean_dec(v_nano_3330_);
                crate::leanh::lean_dec(v___x_3335_);
                v___x_3337_ = lean_int_mul(v___x_3332_, v___x_3334_);
                crate::leanh::lean_dec(v___x_3332_);
                v___x_3338_ = lean_int_add(v___x_3337_, v___x_3333_);
                crate::leanh::lean_dec(v___x_3337_);
                v___x_3339_ = lean_int_add(v___x_3336_, v___x_3338_);
                crate::leanh::lean_dec(v___x_3338_);
                crate::leanh::lean_dec(v___x_3336_);
                v_tm_3340_ = l_Std_Time_Duration_ofNanoseconds(v___x_3339_);
                crate::leanh::lean_dec(v___x_3339_);
                v___x_3341_ = lean_mk_thunk(v___f_3331_);
                if v_isShared_3317_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3316_, 1, v___x_3341_);
                    crate::leanh::lean_ctor_set(v___x_3316_, 0, v_tm_3340_);
                    v___x_3343_ = v___x_3316_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3344_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_tm_3340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3344_, 1, v___x_3341_);
                    v___x_3343_ = v_reuseFailAlloc_3344_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3343_;
            }
            6 => {
                v___x_3364_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_3365_ = lean_int_mod(v_year_3349_, v___x_3364_);
                v___x_3366_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3371_ = lean_int_dec_eq(v___x_3365_, v___x_3366_);
                crate::leanh::lean_dec(v___x_3365_);
                if v___x_3371_ == 0 {
                    v___y_3355_ = v___x_3371_;
                    state = 7;
                    continue;
                } else {
                    v___x_3372_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_3373_ = lean_int_mod(v_year_3349_, v___x_3372_);
                    v___x_3374_ = lean_int_dec_eq(v___x_3373_, v___x_3366_);
                    crate::leanh::lean_dec(v___x_3373_);
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
                    crate::leanh::lean_dec(v_max_3356_);
                    if v_isShared_3353_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3352_, 1, v_month_3313_);
                        v___x_3359_ = v___x_3352_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3360_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 0, v_year_3349_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 1, v_month_3313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3360_, 2, v_day_3350_);
                        v___x_3359_ = v_reuseFailAlloc_3360_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_3350_);
                    if v_isShared_3353_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3352_, 2, v_max_3356_);
                        crate::leanh::lean_ctor_set(v___x_3352_, 1, v_month_3313_);
                        v___x_3362_ = v___x_3352_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3363_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_year_3349_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_month_3313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_max_3356_);
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
                v___x_3368_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_3369_ = lean_int_mod(v_year_3349_, v___x_3368_);
                v___x_3370_ = lean_int_dec_eq(v___x_3369_, v___x_3366_);
                crate::leanh::lean_dec(v___x_3369_);
                v___y_3355_ = v___x_3370_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withMonthClip___boxed(
    mut v_tz_3379_: *mut crate::leanh::LeanObject,
    mut v_dt_3380_: *mut crate::leanh::LeanObject,
    mut v_month_3381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3382_ = l_Std_Time_DateTime_withMonthClip(v_tz_3379_, v_dt_3380_, v_month_3381_);
    crate::leanh::lean_dec_ref(v_tz_3379_);
    return v_res_3382_;
}
pub unsafe fn l_Std_Time_DateTime_withMonthRollOver(
    mut v_tz_3383_: *mut crate::leanh::LeanObject,
    mut v_dt_3384_: *mut crate::leanh::LeanObject,
    mut v_month_3385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3389_: u8 = 0;
    let mut v___x_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3395_: u8 = 0;
    let mut v_year_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3420_: u8 = 0;
    let mut v_isSharedCheck_3421_: u8 = 0;
    let mut v_unused_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3386_ = crate::leanh::lean_ctor_get(v_dt_3384_, 1);
                v_isSharedCheck_3421_ = (!crate::leanh::lean_is_exclusive(v_dt_3384_)) as u8;
                if v_isSharedCheck_3421_ == 0 {
                    v_unused_3422_ = crate::leanh::lean_ctor_get(v_dt_3384_, 0);
                    crate::leanh::lean_dec(v_unused_3422_);
                    v___x_3388_ = v_dt_3384_;
                    v_isShared_3389_ = v_isSharedCheck_3421_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3386_);
                    crate::leanh::lean_dec(v_dt_3384_);
                    v___x_3388_ = crate::leanh::lean_box(0);
                    v_isShared_3389_ = v_isSharedCheck_3421_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3390_ = lean_thunk_get_own(v_date_3386_);
                crate::leanh::lean_dec_ref(v_date_3386_);
                v_date_3391_ = crate::leanh::lean_ctor_get(v___x_3390_, 0);
                v_time_3392_ = crate::leanh::lean_ctor_get(v___x_3390_, 1);
                v_isSharedCheck_3420_ = (!crate::leanh::lean_is_exclusive(v___x_3390_)) as u8;
                if v_isSharedCheck_3420_ == 0 {
                    v___x_3394_ = v___x_3390_;
                    v_isShared_3395_ = v_isSharedCheck_3420_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3392_);
                    crate::leanh::lean_inc(v_date_3391_);
                    crate::leanh::lean_dec(v___x_3390_);
                    v___x_3394_ = crate::leanh::lean_box(0);
                    v_isShared_3395_ = v_isSharedCheck_3420_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_year_3396_ = crate::leanh::lean_ctor_get(v_date_3391_, 0);
                crate::leanh::lean_inc(v_year_3396_);
                v_day_3397_ = crate::leanh::lean_ctor_get(v_date_3391_, 2);
                crate::leanh::lean_inc(v_day_3397_);
                crate::leanh::lean_dec_ref(v_date_3391_);
                v_offset_3398_ = crate::leanh::lean_ctor_get(v_tz_3383_, 0);
                v___x_3399_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3396_, v_month_3385_, v_day_3397_);
                crate::leanh::lean_dec(v_day_3397_);
                if v_isShared_3395_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3394_, 0, v___x_3399_);
                    v___x_3401_ = v___x_3394_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3419_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3419_, 1, v_time_3392_);
                    v___x_3401_ = v_reuseFailAlloc_3419_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3401_);
                v___x_3402_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3401_);
                v_second_3403_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                crate::leanh::lean_inc(v_second_3403_);
                v_nano_3404_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                crate::leanh::lean_inc(v_nano_3404_);
                crate::leanh::lean_dec_ref(v___x_3402_);
                v___f_3405_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3405_, 0, v___x_3401_);
                v___x_3406_ = lean_int_neg(v_offset_3398_);
                v___x_3407_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3408_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3409_ = lean_int_mul(v_second_3403_, v___x_3408_);
                crate::leanh::lean_dec(v_second_3403_);
                v___x_3410_ = lean_int_add(v___x_3409_, v_nano_3404_);
                crate::leanh::lean_dec(v_nano_3404_);
                crate::leanh::lean_dec(v___x_3409_);
                v___x_3411_ = lean_int_mul(v___x_3406_, v___x_3408_);
                crate::leanh::lean_dec(v___x_3406_);
                v___x_3412_ = lean_int_add(v___x_3411_, v___x_3407_);
                crate::leanh::lean_dec(v___x_3411_);
                v___x_3413_ = lean_int_add(v___x_3410_, v___x_3412_);
                crate::leanh::lean_dec(v___x_3412_);
                crate::leanh::lean_dec(v___x_3410_);
                v_tm_3414_ = l_Std_Time_Duration_ofNanoseconds(v___x_3413_);
                crate::leanh::lean_dec(v___x_3413_);
                v___x_3415_ = lean_mk_thunk(v___f_3405_);
                if v_isShared_3389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3388_, 1, v___x_3415_);
                    crate::leanh::lean_ctor_set(v___x_3388_, 0, v_tm_3414_);
                    v___x_3417_ = v___x_3388_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_tm_3414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3418_, 1, v___x_3415_);
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
    mut v_tz_3423_: *mut crate::leanh::LeanObject,
    mut v_dt_3424_: *mut crate::leanh::LeanObject,
    mut v_month_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ = l_Std_Time_DateTime_withMonthRollOver(v_tz_3423_, v_dt_3424_, v_month_3425_);
    crate::leanh::lean_dec_ref(v_tz_3423_);
    return v_res_3426_;
}
pub unsafe fn l_Std_Time_DateTime_withYearClip(
    mut v_tz_3427_: *mut crate::leanh::LeanObject,
    mut v_dt_3428_: *mut crate::leanh::LeanObject,
    mut v_year_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3433_: u8 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v_offset_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3462_: u8 = 0;
    let mut v_unused_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___y_3471_: u8 = 0;
    let mut v_max_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: u8 = 0;
    let mut v___x_3487_: u8 = 0;
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v_isSharedCheck_3491_: u8 = 0;
    let mut v_unused_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut v_unused_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3430_ = crate::leanh::lean_ctor_get(v_dt_3428_, 1);
                v_isSharedCheck_3493_ = (!crate::leanh::lean_is_exclusive(v_dt_3428_)) as u8;
                if v_isSharedCheck_3493_ == 0 {
                    v_unused_3494_ = crate::leanh::lean_ctor_get(v_dt_3428_, 0);
                    crate::leanh::lean_dec(v_unused_3494_);
                    v___x_3432_ = v_dt_3428_;
                    v_isShared_3433_ = v_isSharedCheck_3493_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3430_);
                    crate::leanh::lean_dec(v_dt_3428_);
                    v___x_3432_ = crate::leanh::lean_box(0);
                    v_isShared_3433_ = v_isSharedCheck_3493_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3434_ = lean_thunk_get_own(v_date_3430_);
                crate::leanh::lean_dec_ref(v_date_3430_);
                v_date_3464_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                crate::leanh::lean_inc_ref(v_date_3464_);
                v_month_3465_ = crate::leanh::lean_ctor_get(v_date_3464_, 1);
                v_day_3466_ = crate::leanh::lean_ctor_get(v_date_3464_, 2);
                v_isSharedCheck_3491_ = (!crate::leanh::lean_is_exclusive(v_date_3464_)) as u8;
                if v_isSharedCheck_3491_ == 0 {
                    v_unused_3492_ = crate::leanh::lean_ctor_get(v_date_3464_, 0);
                    crate::leanh::lean_dec(v_unused_3492_);
                    v___x_3468_ = v_date_3464_;
                    v_isShared_3469_ = v_isSharedCheck_3491_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_day_3466_);
                    crate::leanh::lean_inc(v_month_3465_);
                    crate::leanh::lean_dec(v_date_3464_);
                    v___x_3468_ = crate::leanh::lean_box(0);
                    v_isShared_3469_ = v_isSharedCheck_3491_;
                    state = 6;
                    continue;
                }
            }
            2 => {
                v_time_3437_ = crate::leanh::lean_ctor_get(v___x_3434_, 1);
                v_isSharedCheck_3462_ = (!crate::leanh::lean_is_exclusive(v___x_3434_)) as u8;
                if v_isSharedCheck_3462_ == 0 {
                    v_unused_3463_ = crate::leanh::lean_ctor_get(v___x_3434_, 0);
                    crate::leanh::lean_dec(v_unused_3463_);
                    v___x_3439_ = v___x_3434_;
                    v_isShared_3440_ = v_isSharedCheck_3462_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3437_);
                    crate::leanh::lean_dec(v___x_3434_);
                    v___x_3439_ = crate::leanh::lean_box(0);
                    v_isShared_3440_ = v_isSharedCheck_3462_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3441_ = crate::leanh::lean_ctor_get(v_tz_3427_, 0);
                if v_isShared_3440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3439_, 0, v___y_3436_);
                    v___x_3443_ = v___x_3439_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___y_3436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_time_3437_);
                    v___x_3443_ = v_reuseFailAlloc_3461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___x_3443_);
                v___x_3444_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3443_);
                v_second_3445_ = crate::leanh::lean_ctor_get(v___x_3444_, 0);
                crate::leanh::lean_inc(v_second_3445_);
                v_nano_3446_ = crate::leanh::lean_ctor_get(v___x_3444_, 1);
                crate::leanh::lean_inc(v_nano_3446_);
                crate::leanh::lean_dec_ref(v___x_3444_);
                v___f_3447_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3447_, 0, v___x_3443_);
                v___x_3448_ = lean_int_neg(v_offset_3441_);
                v___x_3449_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3450_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3451_ = lean_int_mul(v_second_3445_, v___x_3450_);
                crate::leanh::lean_dec(v_second_3445_);
                v___x_3452_ = lean_int_add(v___x_3451_, v_nano_3446_);
                crate::leanh::lean_dec(v_nano_3446_);
                crate::leanh::lean_dec(v___x_3451_);
                v___x_3453_ = lean_int_mul(v___x_3448_, v___x_3450_);
                crate::leanh::lean_dec(v___x_3448_);
                v___x_3454_ = lean_int_add(v___x_3453_, v___x_3449_);
                crate::leanh::lean_dec(v___x_3453_);
                v___x_3455_ = lean_int_add(v___x_3452_, v___x_3454_);
                crate::leanh::lean_dec(v___x_3454_);
                crate::leanh::lean_dec(v___x_3452_);
                v_tm_3456_ = l_Std_Time_Duration_ofNanoseconds(v___x_3455_);
                crate::leanh::lean_dec(v___x_3455_);
                v___x_3457_ = lean_mk_thunk(v___f_3447_);
                if v_isShared_3433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3432_, 1, v___x_3457_);
                    crate::leanh::lean_ctor_set(v___x_3432_, 0, v_tm_3456_);
                    v___x_3459_ = v___x_3432_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3460_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_tm_3456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3460_, 1, v___x_3457_);
                    v___x_3459_ = v_reuseFailAlloc_3460_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3459_;
            }
            6 => {
                v___x_3480_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_3481_ = lean_int_mod(v_year_3429_, v___x_3480_);
                v___x_3482_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_3487_ = lean_int_dec_eq(v___x_3481_, v___x_3482_);
                crate::leanh::lean_dec(v___x_3481_);
                if v___x_3487_ == 0 {
                    v___y_3471_ = v___x_3487_;
                    state = 7;
                    continue;
                } else {
                    v___x_3488_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_3489_ = lean_int_mod(v_year_3429_, v___x_3488_);
                    v___x_3490_ = lean_int_dec_eq(v___x_3489_, v___x_3482_);
                    crate::leanh::lean_dec(v___x_3489_);
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
                    crate::leanh::lean_dec(v_max_3472_);
                    if v_isShared_3469_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3468_, 0, v_year_3429_);
                        v___x_3475_ = v___x_3468_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_year_3429_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_month_3465_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 2, v_day_3466_);
                        v___x_3475_ = v_reuseFailAlloc_3476_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_day_3466_);
                    if v_isShared_3469_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3468_, 2, v_max_3472_);
                        crate::leanh::lean_ctor_set(v___x_3468_, 0, v_year_3429_);
                        v___x_3478_ = v___x_3468_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3479_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_year_3429_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_month_3465_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_max_3472_);
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
                v___x_3484_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_3485_ = lean_int_mod(v_year_3429_, v___x_3484_);
                v___x_3486_ = lean_int_dec_eq(v___x_3485_, v___x_3482_);
                crate::leanh::lean_dec(v___x_3485_);
                v___y_3471_ = v___x_3486_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_withYearClip___boxed(
    mut v_tz_3495_: *mut crate::leanh::LeanObject,
    mut v_dt_3496_: *mut crate::leanh::LeanObject,
    mut v_year_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ = l_Std_Time_DateTime_withYearClip(v_tz_3495_, v_dt_3496_, v_year_3497_);
    crate::leanh::lean_dec_ref(v_tz_3495_);
    return v_res_3498_;
}
pub unsafe fn l_Std_Time_DateTime_withYearRollOver(
    mut v_tz_3499_: *mut crate::leanh::LeanObject,
    mut v_dt_3500_: *mut crate::leanh::LeanObject,
    mut v_year_3501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v_month_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut v_isSharedCheck_3537_: u8 = 0;
    let mut v_unused_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3502_ = crate::leanh::lean_ctor_get(v_dt_3500_, 1);
                v_isSharedCheck_3537_ = (!crate::leanh::lean_is_exclusive(v_dt_3500_)) as u8;
                if v_isSharedCheck_3537_ == 0 {
                    v_unused_3538_ = crate::leanh::lean_ctor_get(v_dt_3500_, 0);
                    crate::leanh::lean_dec(v_unused_3538_);
                    v___x_3504_ = v_dt_3500_;
                    v_isShared_3505_ = v_isSharedCheck_3537_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3502_);
                    crate::leanh::lean_dec(v_dt_3500_);
                    v___x_3504_ = crate::leanh::lean_box(0);
                    v_isShared_3505_ = v_isSharedCheck_3537_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3506_ = lean_thunk_get_own(v_date_3502_);
                crate::leanh::lean_dec_ref(v_date_3502_);
                v_date_3507_ = crate::leanh::lean_ctor_get(v___x_3506_, 0);
                v_time_3508_ = crate::leanh::lean_ctor_get(v___x_3506_, 1);
                v_isSharedCheck_3536_ = (!crate::leanh::lean_is_exclusive(v___x_3506_)) as u8;
                if v_isSharedCheck_3536_ == 0 {
                    v___x_3510_ = v___x_3506_;
                    v_isShared_3511_ = v_isSharedCheck_3536_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3508_);
                    crate::leanh::lean_inc(v_date_3507_);
                    crate::leanh::lean_dec(v___x_3506_);
                    v___x_3510_ = crate::leanh::lean_box(0);
                    v_isShared_3511_ = v_isSharedCheck_3536_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_3512_ = crate::leanh::lean_ctor_get(v_date_3507_, 1);
                crate::leanh::lean_inc(v_month_3512_);
                v_day_3513_ = crate::leanh::lean_ctor_get(v_date_3507_, 2);
                crate::leanh::lean_inc(v_day_3513_);
                crate::leanh::lean_dec_ref(v_date_3507_);
                v_offset_3514_ = crate::leanh::lean_ctor_get(v_tz_3499_, 0);
                v___x_3515_ =
                    l_Std_Time_PlainDate_rollOver(v_year_3501_, v_month_3512_, v_day_3513_);
                crate::leanh::lean_dec(v_day_3513_);
                if v_isShared_3511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3510_, 0, v___x_3515_);
                    v___x_3517_ = v___x_3510_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 1, v_time_3508_);
                    v___x_3517_ = v_reuseFailAlloc_3535_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___x_3517_);
                v___x_3518_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3517_);
                v_second_3519_ = crate::leanh::lean_ctor_get(v___x_3518_, 0);
                crate::leanh::lean_inc(v_second_3519_);
                v_nano_3520_ = crate::leanh::lean_ctor_get(v___x_3518_, 1);
                crate::leanh::lean_inc(v_nano_3520_);
                crate::leanh::lean_dec_ref(v___x_3518_);
                v___f_3521_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3521_, 0, v___x_3517_);
                v___x_3522_ = lean_int_neg(v_offset_3514_);
                v___x_3523_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3524_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3525_ = lean_int_mul(v_second_3519_, v___x_3524_);
                crate::leanh::lean_dec(v_second_3519_);
                v___x_3526_ = lean_int_add(v___x_3525_, v_nano_3520_);
                crate::leanh::lean_dec(v_nano_3520_);
                crate::leanh::lean_dec(v___x_3525_);
                v___x_3527_ = lean_int_mul(v___x_3522_, v___x_3524_);
                crate::leanh::lean_dec(v___x_3522_);
                v___x_3528_ = lean_int_add(v___x_3527_, v___x_3523_);
                crate::leanh::lean_dec(v___x_3527_);
                v___x_3529_ = lean_int_add(v___x_3526_, v___x_3528_);
                crate::leanh::lean_dec(v___x_3528_);
                crate::leanh::lean_dec(v___x_3526_);
                v_tm_3530_ = l_Std_Time_Duration_ofNanoseconds(v___x_3529_);
                crate::leanh::lean_dec(v___x_3529_);
                v___x_3531_ = lean_mk_thunk(v___f_3521_);
                if v_isShared_3505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3504_, 1, v___x_3531_);
                    crate::leanh::lean_ctor_set(v___x_3504_, 0, v_tm_3530_);
                    v___x_3533_ = v___x_3504_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_tm_3530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 1, v___x_3531_);
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
    mut v_tz_3539_: *mut crate::leanh::LeanObject,
    mut v_dt_3540_: *mut crate::leanh::LeanObject,
    mut v_year_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Std_Time_DateTime_withYearRollOver(v_tz_3539_, v_dt_3540_, v_year_3541_);
    crate::leanh::lean_dec_ref(v_tz_3539_);
    return v_res_3542_;
}
pub unsafe fn l_Std_Time_DateTime_withHours(
    mut v_tz_3543_: *mut crate::leanh::LeanObject,
    mut v_dt_3544_: *mut crate::leanh::LeanObject,
    mut v_hour_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3549_: u8 = 0;
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v_minute_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3561_: u8 = 0;
    let mut v_offset_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3586_: u8 = 0;
    let mut v_unused_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3588_: u8 = 0;
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut v_unused_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3546_ = crate::leanh::lean_ctor_get(v_dt_3544_, 1);
                v_isSharedCheck_3589_ = (!crate::leanh::lean_is_exclusive(v_dt_3544_)) as u8;
                if v_isSharedCheck_3589_ == 0 {
                    v_unused_3590_ = crate::leanh::lean_ctor_get(v_dt_3544_, 0);
                    crate::leanh::lean_dec(v_unused_3590_);
                    v___x_3548_ = v_dt_3544_;
                    v_isShared_3549_ = v_isSharedCheck_3589_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3546_);
                    crate::leanh::lean_dec(v_dt_3544_);
                    v___x_3548_ = crate::leanh::lean_box(0);
                    v_isShared_3549_ = v_isSharedCheck_3589_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3550_ = lean_thunk_get_own(v_date_3546_);
                crate::leanh::lean_dec_ref(v_date_3546_);
                v_time_3551_ = crate::leanh::lean_ctor_get(v___x_3550_, 1);
                v_date_3552_ = crate::leanh::lean_ctor_get(v___x_3550_, 0);
                v_isSharedCheck_3588_ = (!crate::leanh::lean_is_exclusive(v___x_3550_)) as u8;
                if v_isSharedCheck_3588_ == 0 {
                    v___x_3554_ = v___x_3550_;
                    v_isShared_3555_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3551_);
                    crate::leanh::lean_inc(v_date_3552_);
                    crate::leanh::lean_dec(v___x_3550_);
                    v___x_3554_ = crate::leanh::lean_box(0);
                    v_isShared_3555_ = v_isSharedCheck_3588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_minute_3556_ = crate::leanh::lean_ctor_get(v_time_3551_, 1);
                v_second_3557_ = crate::leanh::lean_ctor_get(v_time_3551_, 2);
                v_nanosecond_3558_ = crate::leanh::lean_ctor_get(v_time_3551_, 3);
                v_isSharedCheck_3586_ = (!crate::leanh::lean_is_exclusive(v_time_3551_)) as u8;
                if v_isSharedCheck_3586_ == 0 {
                    v_unused_3587_ = crate::leanh::lean_ctor_get(v_time_3551_, 0);
                    crate::leanh::lean_dec(v_unused_3587_);
                    v___x_3560_ = v_time_3551_;
                    v_isShared_3561_ = v_isSharedCheck_3586_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_3558_);
                    crate::leanh::lean_inc(v_second_3557_);
                    crate::leanh::lean_inc(v_minute_3556_);
                    crate::leanh::lean_dec(v_time_3551_);
                    v___x_3560_ = crate::leanh::lean_box(0);
                    v_isShared_3561_ = v_isSharedCheck_3586_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3562_ = crate::leanh::lean_ctor_get(v_tz_3543_, 0);
                if v_isShared_3561_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3560_, 0, v_hour_3545_);
                    v___x_3564_ = v___x_3560_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3585_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_hour_3545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 1, v_minute_3556_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 2, v_second_3557_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3585_, 3, v_nanosecond_3558_);
                    v___x_3564_ = v_reuseFailAlloc_3585_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3554_, 1, v___x_3564_);
                    v___x_3566_ = v___x_3554_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3584_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_date_3552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3584_, 1, v___x_3564_);
                    v___x_3566_ = v_reuseFailAlloc_3584_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3566_);
                v___x_3567_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3566_);
                v_second_3568_ = crate::leanh::lean_ctor_get(v___x_3567_, 0);
                crate::leanh::lean_inc(v_second_3568_);
                v_nano_3569_ = crate::leanh::lean_ctor_get(v___x_3567_, 1);
                crate::leanh::lean_inc(v_nano_3569_);
                crate::leanh::lean_dec_ref(v___x_3567_);
                v___f_3570_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3570_, 0, v___x_3566_);
                v___x_3571_ = lean_int_neg(v_offset_3562_);
                v___x_3572_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3573_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3574_ = lean_int_mul(v_second_3568_, v___x_3573_);
                crate::leanh::lean_dec(v_second_3568_);
                v___x_3575_ = lean_int_add(v___x_3574_, v_nano_3569_);
                crate::leanh::lean_dec(v_nano_3569_);
                crate::leanh::lean_dec(v___x_3574_);
                v___x_3576_ = lean_int_mul(v___x_3571_, v___x_3573_);
                crate::leanh::lean_dec(v___x_3571_);
                v___x_3577_ = lean_int_add(v___x_3576_, v___x_3572_);
                crate::leanh::lean_dec(v___x_3576_);
                v___x_3578_ = lean_int_add(v___x_3575_, v___x_3577_);
                crate::leanh::lean_dec(v___x_3577_);
                crate::leanh::lean_dec(v___x_3575_);
                v_tm_3579_ = l_Std_Time_Duration_ofNanoseconds(v___x_3578_);
                crate::leanh::lean_dec(v___x_3578_);
                v___x_3580_ = lean_mk_thunk(v___f_3570_);
                if v_isShared_3549_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3548_, 1, v___x_3580_);
                    crate::leanh::lean_ctor_set(v___x_3548_, 0, v_tm_3579_);
                    v___x_3582_ = v___x_3548_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_tm_3579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3583_, 1, v___x_3580_);
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
    mut v_tz_3591_: *mut crate::leanh::LeanObject,
    mut v_dt_3592_: *mut crate::leanh::LeanObject,
    mut v_hour_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3594_ = l_Std_Time_DateTime_withHours(v_tz_3591_, v_dt_3592_, v_hour_3593_);
    crate::leanh::lean_dec_ref(v_tz_3591_);
    return v_res_3594_;
}
pub unsafe fn l_Std_Time_DateTime_withMinutes(
    mut v_tz_3595_: *mut crate::leanh::LeanObject,
    mut v_dt_3596_: *mut crate::leanh::LeanObject,
    mut v_minute_3597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3607_: u8 = 0;
    let mut v_hour_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3613_: u8 = 0;
    let mut v_offset_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_unused_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3640_: u8 = 0;
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v_unused_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3598_ = crate::leanh::lean_ctor_get(v_dt_3596_, 1);
                v_isSharedCheck_3641_ = (!crate::leanh::lean_is_exclusive(v_dt_3596_)) as u8;
                if v_isSharedCheck_3641_ == 0 {
                    v_unused_3642_ = crate::leanh::lean_ctor_get(v_dt_3596_, 0);
                    crate::leanh::lean_dec(v_unused_3642_);
                    v___x_3600_ = v_dt_3596_;
                    v_isShared_3601_ = v_isSharedCheck_3641_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3598_);
                    crate::leanh::lean_dec(v_dt_3596_);
                    v___x_3600_ = crate::leanh::lean_box(0);
                    v_isShared_3601_ = v_isSharedCheck_3641_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3602_ = lean_thunk_get_own(v_date_3598_);
                crate::leanh::lean_dec_ref(v_date_3598_);
                v_time_3603_ = crate::leanh::lean_ctor_get(v___x_3602_, 1);
                v_date_3604_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
                v_isSharedCheck_3640_ = (!crate::leanh::lean_is_exclusive(v___x_3602_)) as u8;
                if v_isSharedCheck_3640_ == 0 {
                    v___x_3606_ = v___x_3602_;
                    v_isShared_3607_ = v_isSharedCheck_3640_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3603_);
                    crate::leanh::lean_inc(v_date_3604_);
                    crate::leanh::lean_dec(v___x_3602_);
                    v___x_3606_ = crate::leanh::lean_box(0);
                    v_isShared_3607_ = v_isSharedCheck_3640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3608_ = crate::leanh::lean_ctor_get(v_time_3603_, 0);
                v_second_3609_ = crate::leanh::lean_ctor_get(v_time_3603_, 2);
                v_nanosecond_3610_ = crate::leanh::lean_ctor_get(v_time_3603_, 3);
                v_isSharedCheck_3638_ = (!crate::leanh::lean_is_exclusive(v_time_3603_)) as u8;
                if v_isSharedCheck_3638_ == 0 {
                    v_unused_3639_ = crate::leanh::lean_ctor_get(v_time_3603_, 1);
                    crate::leanh::lean_dec(v_unused_3639_);
                    v___x_3612_ = v_time_3603_;
                    v_isShared_3613_ = v_isSharedCheck_3638_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_3610_);
                    crate::leanh::lean_inc(v_second_3609_);
                    crate::leanh::lean_inc(v_hour_3608_);
                    crate::leanh::lean_dec(v_time_3603_);
                    v___x_3612_ = crate::leanh::lean_box(0);
                    v_isShared_3613_ = v_isSharedCheck_3638_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3614_ = crate::leanh::lean_ctor_get(v_tz_3595_, 0);
                if v_isShared_3613_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3612_, 1, v_minute_3597_);
                    v___x_3616_ = v___x_3612_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3637_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_hour_3608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_minute_3597_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_second_3609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_nanosecond_3610_);
                    v___x_3616_ = v_reuseFailAlloc_3637_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3607_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3606_, 1, v___x_3616_);
                    v___x_3618_ = v___x_3606_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3636_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_date_3604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3636_, 1, v___x_3616_);
                    v___x_3618_ = v_reuseFailAlloc_3636_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3618_);
                v___x_3619_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3618_);
                v_second_3620_ = crate::leanh::lean_ctor_get(v___x_3619_, 0);
                crate::leanh::lean_inc(v_second_3620_);
                v_nano_3621_ = crate::leanh::lean_ctor_get(v___x_3619_, 1);
                crate::leanh::lean_inc(v_nano_3621_);
                crate::leanh::lean_dec_ref(v___x_3619_);
                v___f_3622_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3622_, 0, v___x_3618_);
                v___x_3623_ = lean_int_neg(v_offset_3614_);
                v___x_3624_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3625_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3626_ = lean_int_mul(v_second_3620_, v___x_3625_);
                crate::leanh::lean_dec(v_second_3620_);
                v___x_3627_ = lean_int_add(v___x_3626_, v_nano_3621_);
                crate::leanh::lean_dec(v_nano_3621_);
                crate::leanh::lean_dec(v___x_3626_);
                v___x_3628_ = lean_int_mul(v___x_3623_, v___x_3625_);
                crate::leanh::lean_dec(v___x_3623_);
                v___x_3629_ = lean_int_add(v___x_3628_, v___x_3624_);
                crate::leanh::lean_dec(v___x_3628_);
                v___x_3630_ = lean_int_add(v___x_3627_, v___x_3629_);
                crate::leanh::lean_dec(v___x_3629_);
                crate::leanh::lean_dec(v___x_3627_);
                v_tm_3631_ = l_Std_Time_Duration_ofNanoseconds(v___x_3630_);
                crate::leanh::lean_dec(v___x_3630_);
                v___x_3632_ = lean_mk_thunk(v___f_3622_);
                if v_isShared_3601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3600_, 1, v___x_3632_);
                    crate::leanh::lean_ctor_set(v___x_3600_, 0, v_tm_3631_);
                    v___x_3634_ = v___x_3600_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3635_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_tm_3631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3635_, 1, v___x_3632_);
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
    mut v_tz_3643_: *mut crate::leanh::LeanObject,
    mut v_dt_3644_: *mut crate::leanh::LeanObject,
    mut v_minute_3645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3646_ = l_Std_Time_DateTime_withMinutes(v_tz_3643_, v_dt_3644_, v_minute_3645_);
    crate::leanh::lean_dec_ref(v_tz_3643_);
    return v_res_3646_;
}
pub unsafe fn l_Std_Time_DateTime_withSeconds(
    mut v_tz_3647_: *mut crate::leanh::LeanObject,
    mut v_dt_3648_: *mut crate::leanh::LeanObject,
    mut v_second_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3653_: u8 = 0;
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v_hour_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_offset_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_unused_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v_unused_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3650_ = crate::leanh::lean_ctor_get(v_dt_3648_, 1);
                v_isSharedCheck_3693_ = (!crate::leanh::lean_is_exclusive(v_dt_3648_)) as u8;
                if v_isSharedCheck_3693_ == 0 {
                    v_unused_3694_ = crate::leanh::lean_ctor_get(v_dt_3648_, 0);
                    crate::leanh::lean_dec(v_unused_3694_);
                    v___x_3652_ = v_dt_3648_;
                    v_isShared_3653_ = v_isSharedCheck_3693_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3650_);
                    crate::leanh::lean_dec(v_dt_3648_);
                    v___x_3652_ = crate::leanh::lean_box(0);
                    v_isShared_3653_ = v_isSharedCheck_3693_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3654_ = lean_thunk_get_own(v_date_3650_);
                crate::leanh::lean_dec_ref(v_date_3650_);
                v_time_3655_ = crate::leanh::lean_ctor_get(v___x_3654_, 1);
                v_date_3656_ = crate::leanh::lean_ctor_get(v___x_3654_, 0);
                v_isSharedCheck_3692_ = (!crate::leanh::lean_is_exclusive(v___x_3654_)) as u8;
                if v_isSharedCheck_3692_ == 0 {
                    v___x_3658_ = v___x_3654_;
                    v_isShared_3659_ = v_isSharedCheck_3692_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3655_);
                    crate::leanh::lean_inc(v_date_3656_);
                    crate::leanh::lean_dec(v___x_3654_);
                    v___x_3658_ = crate::leanh::lean_box(0);
                    v_isShared_3659_ = v_isSharedCheck_3692_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3660_ = crate::leanh::lean_ctor_get(v_time_3655_, 0);
                v_minute_3661_ = crate::leanh::lean_ctor_get(v_time_3655_, 1);
                v_nanosecond_3662_ = crate::leanh::lean_ctor_get(v_time_3655_, 3);
                v_isSharedCheck_3690_ = (!crate::leanh::lean_is_exclusive(v_time_3655_)) as u8;
                if v_isSharedCheck_3690_ == 0 {
                    v_unused_3691_ = crate::leanh::lean_ctor_get(v_time_3655_, 2);
                    crate::leanh::lean_dec(v_unused_3691_);
                    v___x_3664_ = v_time_3655_;
                    v_isShared_3665_ = v_isSharedCheck_3690_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_3662_);
                    crate::leanh::lean_inc(v_minute_3661_);
                    crate::leanh::lean_inc(v_hour_3660_);
                    crate::leanh::lean_dec(v_time_3655_);
                    v___x_3664_ = crate::leanh::lean_box(0);
                    v_isShared_3665_ = v_isSharedCheck_3690_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3666_ = crate::leanh::lean_ctor_get(v_tz_3647_, 0);
                if v_isShared_3665_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3664_, 2, v_second_3649_);
                    v___x_3668_ = v___x_3664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_hour_3660_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 1, v_minute_3661_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 2, v_second_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 3, v_nanosecond_3662_);
                    v___x_3668_ = v_reuseFailAlloc_3689_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3659_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3658_, 1, v___x_3668_);
                    v___x_3670_ = v___x_3658_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3688_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 0, v_date_3656_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3688_, 1, v___x_3668_);
                    v___x_3670_ = v_reuseFailAlloc_3688_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3670_);
                v___x_3671_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3670_);
                v_second_3672_ = crate::leanh::lean_ctor_get(v___x_3671_, 0);
                crate::leanh::lean_inc(v_second_3672_);
                v_nano_3673_ = crate::leanh::lean_ctor_get(v___x_3671_, 1);
                crate::leanh::lean_inc(v_nano_3673_);
                crate::leanh::lean_dec_ref(v___x_3671_);
                v___f_3674_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3674_, 0, v___x_3670_);
                v___x_3675_ = lean_int_neg(v_offset_3666_);
                v___x_3676_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3677_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3678_ = lean_int_mul(v_second_3672_, v___x_3677_);
                crate::leanh::lean_dec(v_second_3672_);
                v___x_3679_ = lean_int_add(v___x_3678_, v_nano_3673_);
                crate::leanh::lean_dec(v_nano_3673_);
                crate::leanh::lean_dec(v___x_3678_);
                v___x_3680_ = lean_int_mul(v___x_3675_, v___x_3677_);
                crate::leanh::lean_dec(v___x_3675_);
                v___x_3681_ = lean_int_add(v___x_3680_, v___x_3676_);
                crate::leanh::lean_dec(v___x_3680_);
                v___x_3682_ = lean_int_add(v___x_3679_, v___x_3681_);
                crate::leanh::lean_dec(v___x_3681_);
                crate::leanh::lean_dec(v___x_3679_);
                v_tm_3683_ = l_Std_Time_Duration_ofNanoseconds(v___x_3682_);
                crate::leanh::lean_dec(v___x_3682_);
                v___x_3684_ = lean_mk_thunk(v___f_3674_);
                if v_isShared_3653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3652_, 1, v___x_3684_);
                    crate::leanh::lean_ctor_set(v___x_3652_, 0, v_tm_3683_);
                    v___x_3686_ = v___x_3652_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_tm_3683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3684_);
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
    mut v_tz_3695_: *mut crate::leanh::LeanObject,
    mut v_dt_3696_: *mut crate::leanh::LeanObject,
    mut v_second_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3698_ = l_Std_Time_DateTime_withSeconds(v_tz_3695_, v_dt_3696_, v_second_3697_);
    crate::leanh::lean_dec_ref(v_tz_3695_);
    return v_res_3698_;
}
pub unsafe fn l_Std_Time_DateTime_withNanoseconds(
    mut v_tz_3699_: *mut crate::leanh::LeanObject,
    mut v_dt_3700_: *mut crate::leanh::LeanObject,
    mut v_nano_3701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v_hour_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3717_: u8 = 0;
    let mut v_offset_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut v_unused_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3744_: u8 = 0;
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v_unused_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3702_ = crate::leanh::lean_ctor_get(v_dt_3700_, 1);
                v_isSharedCheck_3745_ = (!crate::leanh::lean_is_exclusive(v_dt_3700_)) as u8;
                if v_isSharedCheck_3745_ == 0 {
                    v_unused_3746_ = crate::leanh::lean_ctor_get(v_dt_3700_, 0);
                    crate::leanh::lean_dec(v_unused_3746_);
                    v___x_3704_ = v_dt_3700_;
                    v_isShared_3705_ = v_isSharedCheck_3745_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3702_);
                    crate::leanh::lean_dec(v_dt_3700_);
                    v___x_3704_ = crate::leanh::lean_box(0);
                    v_isShared_3705_ = v_isSharedCheck_3745_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3706_ = lean_thunk_get_own(v_date_3702_);
                crate::leanh::lean_dec_ref(v_date_3702_);
                v_time_3707_ = crate::leanh::lean_ctor_get(v___x_3706_, 1);
                v_date_3708_ = crate::leanh::lean_ctor_get(v___x_3706_, 0);
                v_isSharedCheck_3744_ = (!crate::leanh::lean_is_exclusive(v___x_3706_)) as u8;
                if v_isSharedCheck_3744_ == 0 {
                    v___x_3710_ = v___x_3706_;
                    v_isShared_3711_ = v_isSharedCheck_3744_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3707_);
                    crate::leanh::lean_inc(v_date_3708_);
                    crate::leanh::lean_dec(v___x_3706_);
                    v___x_3710_ = crate::leanh::lean_box(0);
                    v_isShared_3711_ = v_isSharedCheck_3744_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3712_ = crate::leanh::lean_ctor_get(v_time_3707_, 0);
                v_minute_3713_ = crate::leanh::lean_ctor_get(v_time_3707_, 1);
                v_second_3714_ = crate::leanh::lean_ctor_get(v_time_3707_, 2);
                v_isSharedCheck_3742_ = (!crate::leanh::lean_is_exclusive(v_time_3707_)) as u8;
                if v_isSharedCheck_3742_ == 0 {
                    v_unused_3743_ = crate::leanh::lean_ctor_get(v_time_3707_, 3);
                    crate::leanh::lean_dec(v_unused_3743_);
                    v___x_3716_ = v_time_3707_;
                    v_isShared_3717_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_second_3714_);
                    crate::leanh::lean_inc(v_minute_3713_);
                    crate::leanh::lean_inc(v_hour_3712_);
                    crate::leanh::lean_dec(v_time_3707_);
                    v___x_3716_ = crate::leanh::lean_box(0);
                    v_isShared_3717_ = v_isSharedCheck_3742_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3718_ = crate::leanh::lean_ctor_get(v_tz_3699_, 0);
                if v_isShared_3717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3716_, 3, v_nano_3701_);
                    v___x_3720_ = v___x_3716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_hour_3712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 1, v_minute_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 2, v_second_3714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 3, v_nano_3701_);
                    v___x_3720_ = v_reuseFailAlloc_3741_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3711_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3710_, 1, v___x_3720_);
                    v___x_3722_ = v___x_3710_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3740_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_date_3708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3740_, 1, v___x_3720_);
                    v___x_3722_ = v_reuseFailAlloc_3740_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3722_);
                v___x_3723_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3722_);
                v_second_3724_ = crate::leanh::lean_ctor_get(v___x_3723_, 0);
                crate::leanh::lean_inc(v_second_3724_);
                v_nano_3725_ = crate::leanh::lean_ctor_get(v___x_3723_, 1);
                crate::leanh::lean_inc(v_nano_3725_);
                crate::leanh::lean_dec_ref(v___x_3723_);
                v___f_3726_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3726_, 0, v___x_3722_);
                v___x_3727_ = lean_int_neg(v_offset_3718_);
                v___x_3728_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3729_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3730_ = lean_int_mul(v_second_3724_, v___x_3729_);
                crate::leanh::lean_dec(v_second_3724_);
                v___x_3731_ = lean_int_add(v___x_3730_, v_nano_3725_);
                crate::leanh::lean_dec(v_nano_3725_);
                crate::leanh::lean_dec(v___x_3730_);
                v___x_3732_ = lean_int_mul(v___x_3727_, v___x_3729_);
                crate::leanh::lean_dec(v___x_3727_);
                v___x_3733_ = lean_int_add(v___x_3732_, v___x_3728_);
                crate::leanh::lean_dec(v___x_3732_);
                v___x_3734_ = lean_int_add(v___x_3731_, v___x_3733_);
                crate::leanh::lean_dec(v___x_3733_);
                crate::leanh::lean_dec(v___x_3731_);
                v_tm_3735_ = l_Std_Time_Duration_ofNanoseconds(v___x_3734_);
                crate::leanh::lean_dec(v___x_3734_);
                v___x_3736_ = lean_mk_thunk(v___f_3726_);
                if v_isShared_3705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3704_, 1, v___x_3736_);
                    crate::leanh::lean_ctor_set(v___x_3704_, 0, v_tm_3735_);
                    v___x_3738_ = v___x_3704_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3739_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_tm_3735_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3739_, 1, v___x_3736_);
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
    mut v_tz_3747_: *mut crate::leanh::LeanObject,
    mut v_dt_3748_: *mut crate::leanh::LeanObject,
    mut v_nano_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3750_ = l_Std_Time_DateTime_withNanoseconds(v_tz_3747_, v_dt_3748_, v_nano_3749_);
    crate::leanh::lean_dec_ref(v_tz_3747_);
    return v_res_3750_;
}
pub unsafe fn _init_l_Std_Time_DateTime_withMilliseconds___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3751_ = crate::leanh::lean_unsigned_to_nat(1000);
    v___x_3752_ = lean_nat_to_int(v___x_3751_);
    return v___x_3752_;
}
pub unsafe fn l_Std_Time_DateTime_withMilliseconds(
    mut v_tz_3753_: *mut crate::leanh::LeanObject,
    mut v_dt_3754_: *mut crate::leanh::LeanObject,
    mut v_milli_3755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3759_: u8 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v_hour_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3772_: u8 = 0;
    let mut v_offset_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut v_isSharedCheck_3804_: u8 = 0;
    let mut v_unused_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3756_ = crate::leanh::lean_ctor_get(v_dt_3754_, 1);
                v_isSharedCheck_3804_ = (!crate::leanh::lean_is_exclusive(v_dt_3754_)) as u8;
                if v_isSharedCheck_3804_ == 0 {
                    v_unused_3805_ = crate::leanh::lean_ctor_get(v_dt_3754_, 0);
                    crate::leanh::lean_dec(v_unused_3805_);
                    v___x_3758_ = v_dt_3754_;
                    v_isShared_3759_ = v_isSharedCheck_3804_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3756_);
                    crate::leanh::lean_dec(v_dt_3754_);
                    v___x_3758_ = crate::leanh::lean_box(0);
                    v_isShared_3759_ = v_isSharedCheck_3804_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3760_ = lean_thunk_get_own(v_date_3756_);
                crate::leanh::lean_dec_ref(v_date_3756_);
                v_time_3761_ = crate::leanh::lean_ctor_get(v___x_3760_, 1);
                v_date_3762_ = crate::leanh::lean_ctor_get(v___x_3760_, 0);
                v_isSharedCheck_3803_ = (!crate::leanh::lean_is_exclusive(v___x_3760_)) as u8;
                if v_isSharedCheck_3803_ == 0 {
                    v___x_3764_ = v___x_3760_;
                    v_isShared_3765_ = v_isSharedCheck_3803_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_time_3761_);
                    crate::leanh::lean_inc(v_date_3762_);
                    crate::leanh::lean_dec(v___x_3760_);
                    v___x_3764_ = crate::leanh::lean_box(0);
                    v_isShared_3765_ = v_isSharedCheck_3803_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_hour_3766_ = crate::leanh::lean_ctor_get(v_time_3761_, 0);
                v_minute_3767_ = crate::leanh::lean_ctor_get(v_time_3761_, 1);
                v_second_3768_ = crate::leanh::lean_ctor_get(v_time_3761_, 2);
                v_nanosecond_3769_ = crate::leanh::lean_ctor_get(v_time_3761_, 3);
                v_isSharedCheck_3802_ = (!crate::leanh::lean_is_exclusive(v_time_3761_)) as u8;
                if v_isSharedCheck_3802_ == 0 {
                    v___x_3771_ = v_time_3761_;
                    v_isShared_3772_ = v_isSharedCheck_3802_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nanosecond_3769_);
                    crate::leanh::lean_inc(v_second_3768_);
                    crate::leanh::lean_inc(v_minute_3767_);
                    crate::leanh::lean_inc(v_hour_3766_);
                    crate::leanh::lean_dec(v_time_3761_);
                    v___x_3771_ = crate::leanh::lean_box(0);
                    v_isShared_3772_ = v_isSharedCheck_3802_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_offset_3773_ = crate::leanh::lean_ctor_get(v_tz_3753_, 0);
                v___x_3774_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_withMilliseconds___closed__0,
                );
                v___x_3775_ = lean_int_emod(v_nanosecond_3769_, v___x_3774_);
                crate::leanh::lean_dec(v_nanosecond_3769_);
                v___x_3776_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_addMilliseconds___closed__0_once),
                    _init_l_Std_Time_DateTime_addMilliseconds___closed__0,
                );
                v___x_3777_ = lean_int_mul(v_milli_3755_, v___x_3776_);
                v___x_3778_ = lean_int_add(v___x_3777_, v___x_3775_);
                crate::leanh::lean_dec(v___x_3775_);
                crate::leanh::lean_dec(v___x_3777_);
                if v_isShared_3772_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3771_, 3, v___x_3778_);
                    v___x_3780_ = v___x_3771_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3801_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_hour_3766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 1, v_minute_3767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 2, v_second_3768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 3, v___x_3778_);
                    v___x_3780_ = v_reuseFailAlloc_3801_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3764_, 1, v___x_3780_);
                    v___x_3782_ = v___x_3764_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3800_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_date_3762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3800_, 1, v___x_3780_);
                    v___x_3782_ = v_reuseFailAlloc_3800_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___x_3782_);
                v___x_3783_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3782_);
                v_second_3784_ = crate::leanh::lean_ctor_get(v___x_3783_, 0);
                crate::leanh::lean_inc(v_second_3784_);
                v_nano_3785_ = crate::leanh::lean_ctor_get(v___x_3783_, 1);
                crate::leanh::lean_inc(v_nano_3785_);
                crate::leanh::lean_dec_ref(v___x_3783_);
                v___f_3786_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3786_, 0, v___x_3782_);
                v___x_3787_ = lean_int_neg(v_offset_3773_);
                v___x_3788_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_3789_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_3790_ = lean_int_mul(v_second_3784_, v___x_3789_);
                crate::leanh::lean_dec(v_second_3784_);
                v___x_3791_ = lean_int_add(v___x_3790_, v_nano_3785_);
                crate::leanh::lean_dec(v_nano_3785_);
                crate::leanh::lean_dec(v___x_3790_);
                v___x_3792_ = lean_int_mul(v___x_3787_, v___x_3789_);
                crate::leanh::lean_dec(v___x_3787_);
                v___x_3793_ = lean_int_add(v___x_3792_, v___x_3788_);
                crate::leanh::lean_dec(v___x_3792_);
                v___x_3794_ = lean_int_add(v___x_3791_, v___x_3793_);
                crate::leanh::lean_dec(v___x_3793_);
                crate::leanh::lean_dec(v___x_3791_);
                v_tm_3795_ = l_Std_Time_Duration_ofNanoseconds(v___x_3794_);
                crate::leanh::lean_dec(v___x_3794_);
                v___x_3796_ = lean_mk_thunk(v___f_3786_);
                if v_isShared_3759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3758_, 1, v___x_3796_);
                    crate::leanh::lean_ctor_set(v___x_3758_, 0, v_tm_3795_);
                    v___x_3798_ = v___x_3758_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3799_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_tm_3795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 1, v___x_3796_);
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
    mut v_tz_3806_: *mut crate::leanh::LeanObject,
    mut v_dt_3807_: *mut crate::leanh::LeanObject,
    mut v_milli_3808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3809_ = l_Std_Time_DateTime_withMilliseconds(v_tz_3806_, v_dt_3807_, v_milli_3808_);
    crate::leanh::lean_dec(v_milli_3808_);
    crate::leanh::lean_dec_ref(v_tz_3806_);
    return v_res_3809_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime___redArg(
    mut v_dt_3810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3811_ = crate::leanh::lean_ctor_get(v_dt_3810_, 1);
    v___x_3812_ = lean_thunk_get_own(v_date_3811_);
    return v___x_3812_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime___redArg___boxed(
    mut v_dt_3813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3814_ = l_Std_Time_DateTime_toPlainDateTime___redArg(v_dt_3813_);
    crate::leanh::lean_dec_ref(v_dt_3813_);
    return v_res_3814_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime(
    mut v_tz_3815_: *mut crate::leanh::LeanObject,
    mut v_dt_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3817_ = crate::leanh::lean_ctor_get(v_dt_3816_, 1);
    v___x_3818_ = lean_thunk_get_own(v_date_3817_);
    return v___x_3818_;
}
pub unsafe fn l_Std_Time_DateTime_toPlainDateTime___boxed(
    mut v_tz_3819_: *mut crate::leanh::LeanObject,
    mut v_dt_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Std_Time_DateTime_toPlainDateTime(v_tz_3819_, v_dt_3820_);
    crate::leanh::lean_dec_ref(v_dt_3820_);
    crate::leanh::lean_dec_ref(v_tz_3819_);
    return v_res_3821_;
}
pub unsafe fn l_Std_Time_DateTime_year___redArg(
    mut v_dt_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3823_ = crate::leanh::lean_ctor_get(v_dt_3822_, 1);
    v___x_3824_ = lean_thunk_get_own(v_date_3823_);
    v_date_3825_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
    crate::leanh::lean_inc_ref(v_date_3825_);
    crate::leanh::lean_dec(v___x_3824_);
    v_year_3826_ = crate::leanh::lean_ctor_get(v_date_3825_, 0);
    crate::leanh::lean_inc(v_year_3826_);
    crate::leanh::lean_dec_ref(v_date_3825_);
    return v_year_3826_;
}
pub unsafe fn l_Std_Time_DateTime_year___redArg___boxed(
    mut v_dt_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3828_ = l_Std_Time_DateTime_year___redArg(v_dt_3827_);
    crate::leanh::lean_dec_ref(v_dt_3827_);
    return v_res_3828_;
}
pub unsafe fn l_Std_Time_DateTime_year(
    mut v_tz_3829_: *mut crate::leanh::LeanObject,
    mut v_dt_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3831_ = crate::leanh::lean_ctor_get(v_dt_3830_, 1);
    v___x_3832_ = lean_thunk_get_own(v_date_3831_);
    v_date_3833_ = crate::leanh::lean_ctor_get(v___x_3832_, 0);
    crate::leanh::lean_inc_ref(v_date_3833_);
    crate::leanh::lean_dec(v___x_3832_);
    v_year_3834_ = crate::leanh::lean_ctor_get(v_date_3833_, 0);
    crate::leanh::lean_inc(v_year_3834_);
    crate::leanh::lean_dec_ref(v_date_3833_);
    return v_year_3834_;
}
pub unsafe fn l_Std_Time_DateTime_year___boxed(
    mut v_tz_3835_: *mut crate::leanh::LeanObject,
    mut v_dt_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3837_ = l_Std_Time_DateTime_year(v_tz_3835_, v_dt_3836_);
    crate::leanh::lean_dec_ref(v_dt_3836_);
    crate::leanh::lean_dec_ref(v_tz_3835_);
    return v_res_3837_;
}
pub unsafe fn l_Std_Time_DateTime_month___redArg(
    mut v_dt_3838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3839_ = crate::leanh::lean_ctor_get(v_dt_3838_, 1);
    v___x_3840_ = lean_thunk_get_own(v_date_3839_);
    v_date_3841_ = crate::leanh::lean_ctor_get(v___x_3840_, 0);
    crate::leanh::lean_inc_ref(v_date_3841_);
    crate::leanh::lean_dec(v___x_3840_);
    v_month_3842_ = crate::leanh::lean_ctor_get(v_date_3841_, 1);
    crate::leanh::lean_inc(v_month_3842_);
    crate::leanh::lean_dec_ref(v_date_3841_);
    return v_month_3842_;
}
pub unsafe fn l_Std_Time_DateTime_month___redArg___boxed(
    mut v_dt_3843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3844_ = l_Std_Time_DateTime_month___redArg(v_dt_3843_);
    crate::leanh::lean_dec_ref(v_dt_3843_);
    return v_res_3844_;
}
pub unsafe fn l_Std_Time_DateTime_month(
    mut v_tz_3845_: *mut crate::leanh::LeanObject,
    mut v_dt_3846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_month_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3847_ = crate::leanh::lean_ctor_get(v_dt_3846_, 1);
    v___x_3848_ = lean_thunk_get_own(v_date_3847_);
    v_date_3849_ = crate::leanh::lean_ctor_get(v___x_3848_, 0);
    crate::leanh::lean_inc_ref(v_date_3849_);
    crate::leanh::lean_dec(v___x_3848_);
    v_month_3850_ = crate::leanh::lean_ctor_get(v_date_3849_, 1);
    crate::leanh::lean_inc(v_month_3850_);
    crate::leanh::lean_dec_ref(v_date_3849_);
    return v_month_3850_;
}
pub unsafe fn l_Std_Time_DateTime_month___boxed(
    mut v_tz_3851_: *mut crate::leanh::LeanObject,
    mut v_dt_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Std_Time_DateTime_month(v_tz_3851_, v_dt_3852_);
    crate::leanh::lean_dec_ref(v_dt_3852_);
    crate::leanh::lean_dec_ref(v_tz_3851_);
    return v_res_3853_;
}
pub unsafe fn l_Std_Time_DateTime_day___redArg(
    mut v_dt_3854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3855_ = crate::leanh::lean_ctor_get(v_dt_3854_, 1);
    v___x_3856_ = lean_thunk_get_own(v_date_3855_);
    v_date_3857_ = crate::leanh::lean_ctor_get(v___x_3856_, 0);
    crate::leanh::lean_inc_ref(v_date_3857_);
    crate::leanh::lean_dec(v___x_3856_);
    v_day_3858_ = crate::leanh::lean_ctor_get(v_date_3857_, 2);
    crate::leanh::lean_inc(v_day_3858_);
    crate::leanh::lean_dec_ref(v_date_3857_);
    return v_day_3858_;
}
pub unsafe fn l_Std_Time_DateTime_day___redArg___boxed(
    mut v_dt_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3860_ = l_Std_Time_DateTime_day___redArg(v_dt_3859_);
    crate::leanh::lean_dec_ref(v_dt_3859_);
    return v_res_3860_;
}
pub unsafe fn l_Std_Time_DateTime_day(
    mut v_tz_3861_: *mut crate::leanh::LeanObject,
    mut v_dt_3862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3863_ = crate::leanh::lean_ctor_get(v_dt_3862_, 1);
    v___x_3864_ = lean_thunk_get_own(v_date_3863_);
    v_date_3865_ = crate::leanh::lean_ctor_get(v___x_3864_, 0);
    crate::leanh::lean_inc_ref(v_date_3865_);
    crate::leanh::lean_dec(v___x_3864_);
    v_day_3866_ = crate::leanh::lean_ctor_get(v_date_3865_, 2);
    crate::leanh::lean_inc(v_day_3866_);
    crate::leanh::lean_dec_ref(v_date_3865_);
    return v_day_3866_;
}
pub unsafe fn l_Std_Time_DateTime_day___boxed(
    mut v_tz_3867_: *mut crate::leanh::LeanObject,
    mut v_dt_3868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3869_ = l_Std_Time_DateTime_day(v_tz_3867_, v_dt_3868_);
    crate::leanh::lean_dec_ref(v_dt_3868_);
    crate::leanh::lean_dec_ref(v_tz_3867_);
    return v_res_3869_;
}
pub unsafe fn l_Std_Time_DateTime_hour___redArg(
    mut v_dt_3870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3871_ = crate::leanh::lean_ctor_get(v_dt_3870_, 1);
    v___x_3872_ = lean_thunk_get_own(v_date_3871_);
    v_time_3873_ = crate::leanh::lean_ctor_get(v___x_3872_, 1);
    crate::leanh::lean_inc_ref(v_time_3873_);
    crate::leanh::lean_dec(v___x_3872_);
    v_hour_3874_ = crate::leanh::lean_ctor_get(v_time_3873_, 0);
    crate::leanh::lean_inc(v_hour_3874_);
    crate::leanh::lean_dec_ref(v_time_3873_);
    return v_hour_3874_;
}
pub unsafe fn l_Std_Time_DateTime_hour___redArg___boxed(
    mut v_dt_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3876_ = l_Std_Time_DateTime_hour___redArg(v_dt_3875_);
    crate::leanh::lean_dec_ref(v_dt_3875_);
    return v_res_3876_;
}
pub unsafe fn l_Std_Time_DateTime_hour(
    mut v_tz_3877_: *mut crate::leanh::LeanObject,
    mut v_dt_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hour_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3879_ = crate::leanh::lean_ctor_get(v_dt_3878_, 1);
    v___x_3880_ = lean_thunk_get_own(v_date_3879_);
    v_time_3881_ = crate::leanh::lean_ctor_get(v___x_3880_, 1);
    crate::leanh::lean_inc_ref(v_time_3881_);
    crate::leanh::lean_dec(v___x_3880_);
    v_hour_3882_ = crate::leanh::lean_ctor_get(v_time_3881_, 0);
    crate::leanh::lean_inc(v_hour_3882_);
    crate::leanh::lean_dec_ref(v_time_3881_);
    return v_hour_3882_;
}
pub unsafe fn l_Std_Time_DateTime_hour___boxed(
    mut v_tz_3883_: *mut crate::leanh::LeanObject,
    mut v_dt_3884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3885_ = l_Std_Time_DateTime_hour(v_tz_3883_, v_dt_3884_);
    crate::leanh::lean_dec_ref(v_dt_3884_);
    crate::leanh::lean_dec_ref(v_tz_3883_);
    return v_res_3885_;
}
pub unsafe fn l_Std_Time_DateTime_minute___redArg(
    mut v_dt_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3887_ = crate::leanh::lean_ctor_get(v_dt_3886_, 1);
    v___x_3888_ = lean_thunk_get_own(v_date_3887_);
    v_time_3889_ = crate::leanh::lean_ctor_get(v___x_3888_, 1);
    crate::leanh::lean_inc_ref(v_time_3889_);
    crate::leanh::lean_dec(v___x_3888_);
    v_minute_3890_ = crate::leanh::lean_ctor_get(v_time_3889_, 1);
    crate::leanh::lean_inc(v_minute_3890_);
    crate::leanh::lean_dec_ref(v_time_3889_);
    return v_minute_3890_;
}
pub unsafe fn l_Std_Time_DateTime_minute___redArg___boxed(
    mut v_dt_3891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3892_ = l_Std_Time_DateTime_minute___redArg(v_dt_3891_);
    crate::leanh::lean_dec_ref(v_dt_3891_);
    return v_res_3892_;
}
pub unsafe fn l_Std_Time_DateTime_minute(
    mut v_tz_3893_: *mut crate::leanh::LeanObject,
    mut v_dt_3894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_minute_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3895_ = crate::leanh::lean_ctor_get(v_dt_3894_, 1);
    v___x_3896_ = lean_thunk_get_own(v_date_3895_);
    v_time_3897_ = crate::leanh::lean_ctor_get(v___x_3896_, 1);
    crate::leanh::lean_inc_ref(v_time_3897_);
    crate::leanh::lean_dec(v___x_3896_);
    v_minute_3898_ = crate::leanh::lean_ctor_get(v_time_3897_, 1);
    crate::leanh::lean_inc(v_minute_3898_);
    crate::leanh::lean_dec_ref(v_time_3897_);
    return v_minute_3898_;
}
pub unsafe fn l_Std_Time_DateTime_minute___boxed(
    mut v_tz_3899_: *mut crate::leanh::LeanObject,
    mut v_dt_3900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3901_ = l_Std_Time_DateTime_minute(v_tz_3899_, v_dt_3900_);
    crate::leanh::lean_dec_ref(v_dt_3900_);
    crate::leanh::lean_dec_ref(v_tz_3899_);
    return v_res_3901_;
}
pub unsafe fn l_Std_Time_DateTime_second___redArg(
    mut v_dt_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3903_ = crate::leanh::lean_ctor_get(v_dt_3902_, 1);
    v___x_3904_ = lean_thunk_get_own(v_date_3903_);
    v_time_3905_ = crate::leanh::lean_ctor_get(v___x_3904_, 1);
    crate::leanh::lean_inc_ref(v_time_3905_);
    crate::leanh::lean_dec(v___x_3904_);
    v_second_3906_ = crate::leanh::lean_ctor_get(v_time_3905_, 2);
    crate::leanh::lean_inc(v_second_3906_);
    crate::leanh::lean_dec_ref(v_time_3905_);
    return v_second_3906_;
}
pub unsafe fn l_Std_Time_DateTime_second___redArg___boxed(
    mut v_dt_3907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3908_ = l_Std_Time_DateTime_second___redArg(v_dt_3907_);
    crate::leanh::lean_dec_ref(v_dt_3907_);
    return v_res_3908_;
}
pub unsafe fn l_Std_Time_DateTime_second(
    mut v_tz_3909_: *mut crate::leanh::LeanObject,
    mut v_dt_3910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3911_ = crate::leanh::lean_ctor_get(v_dt_3910_, 1);
    v___x_3912_ = lean_thunk_get_own(v_date_3911_);
    v_time_3913_ = crate::leanh::lean_ctor_get(v___x_3912_, 1);
    crate::leanh::lean_inc_ref(v_time_3913_);
    crate::leanh::lean_dec(v___x_3912_);
    v_second_3914_ = crate::leanh::lean_ctor_get(v_time_3913_, 2);
    crate::leanh::lean_inc(v_second_3914_);
    crate::leanh::lean_dec_ref(v_time_3913_);
    return v_second_3914_;
}
pub unsafe fn l_Std_Time_DateTime_second___boxed(
    mut v_tz_3915_: *mut crate::leanh::LeanObject,
    mut v_dt_3916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3917_ = l_Std_Time_DateTime_second(v_tz_3915_, v_dt_3916_);
    crate::leanh::lean_dec_ref(v_dt_3916_);
    crate::leanh::lean_dec_ref(v_tz_3915_);
    return v_res_3917_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond___redArg(
    mut v_dt_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3919_ = crate::leanh::lean_ctor_get(v_dt_3918_, 1);
    v___x_3920_ = lean_thunk_get_own(v_date_3919_);
    v_time_3921_ = crate::leanh::lean_ctor_get(v___x_3920_, 1);
    crate::leanh::lean_inc_ref(v_time_3921_);
    crate::leanh::lean_dec(v___x_3920_);
    v_nanosecond_3922_ = crate::leanh::lean_ctor_get(v_time_3921_, 3);
    crate::leanh::lean_inc(v_nanosecond_3922_);
    crate::leanh::lean_dec_ref(v_time_3921_);
    v___x_3923_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0_once),
        _init_l_Std_Time_DateTime_withMilliseconds___closed__0,
    );
    v___x_3924_ = lean_int_emod(v_nanosecond_3922_, v___x_3923_);
    crate::leanh::lean_dec(v_nanosecond_3922_);
    return v___x_3924_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond___redArg___boxed(
    mut v_dt_3925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3926_ = l_Std_Time_DateTime_millisecond___redArg(v_dt_3925_);
    crate::leanh::lean_dec_ref(v_dt_3925_);
    return v_res_3926_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond(
    mut v_tz_3927_: *mut crate::leanh::LeanObject,
    mut v_dt_3928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3929_ = crate::leanh::lean_ctor_get(v_dt_3928_, 1);
    v___x_3930_ = lean_thunk_get_own(v_date_3929_);
    v_time_3931_ = crate::leanh::lean_ctor_get(v___x_3930_, 1);
    crate::leanh::lean_inc_ref(v_time_3931_);
    crate::leanh::lean_dec(v___x_3930_);
    v_nanosecond_3932_ = crate::leanh::lean_ctor_get(v_time_3931_, 3);
    crate::leanh::lean_inc(v_nanosecond_3932_);
    crate::leanh::lean_dec_ref(v_time_3931_);
    v___x_3933_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withMilliseconds___closed__0_once),
        _init_l_Std_Time_DateTime_withMilliseconds___closed__0,
    );
    v___x_3934_ = lean_int_emod(v_nanosecond_3932_, v___x_3933_);
    crate::leanh::lean_dec(v_nanosecond_3932_);
    return v___x_3934_;
}
pub unsafe fn l_Std_Time_DateTime_millisecond___boxed(
    mut v_tz_3935_: *mut crate::leanh::LeanObject,
    mut v_dt_3936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3937_ = l_Std_Time_DateTime_millisecond(v_tz_3935_, v_dt_3936_);
    crate::leanh::lean_dec_ref(v_dt_3936_);
    crate::leanh::lean_dec_ref(v_tz_3935_);
    return v_res_3937_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond___redArg(
    mut v_dt_3938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3939_ = crate::leanh::lean_ctor_get(v_dt_3938_, 1);
    v___x_3940_ = lean_thunk_get_own(v_date_3939_);
    v_time_3941_ = crate::leanh::lean_ctor_get(v___x_3940_, 1);
    crate::leanh::lean_inc_ref(v_time_3941_);
    crate::leanh::lean_dec(v___x_3940_);
    v_nanosecond_3942_ = crate::leanh::lean_ctor_get(v_time_3941_, 3);
    crate::leanh::lean_inc(v_nanosecond_3942_);
    crate::leanh::lean_dec_ref(v_time_3941_);
    return v_nanosecond_3942_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond___redArg___boxed(
    mut v_dt_3943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3944_ = l_Std_Time_DateTime_nanosecond___redArg(v_dt_3943_);
    crate::leanh::lean_dec_ref(v_dt_3943_);
    return v_res_3944_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond(
    mut v_tz_3945_: *mut crate::leanh::LeanObject,
    mut v_dt_3946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanosecond_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_3947_ = crate::leanh::lean_ctor_get(v_dt_3946_, 1);
    v___x_3948_ = lean_thunk_get_own(v_date_3947_);
    v_time_3949_ = crate::leanh::lean_ctor_get(v___x_3948_, 1);
    crate::leanh::lean_inc_ref(v_time_3949_);
    crate::leanh::lean_dec(v___x_3948_);
    v_nanosecond_3950_ = crate::leanh::lean_ctor_get(v_time_3949_, 3);
    crate::leanh::lean_inc(v_nanosecond_3950_);
    crate::leanh::lean_dec_ref(v_time_3949_);
    return v_nanosecond_3950_;
}
pub unsafe fn l_Std_Time_DateTime_nanosecond___boxed(
    mut v_tz_3951_: *mut crate::leanh::LeanObject,
    mut v_dt_3952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Std_Time_DateTime_nanosecond(v_tz_3951_, v_dt_3952_);
    crate::leanh::lean_dec_ref(v_dt_3952_);
    crate::leanh::lean_dec_ref(v_tz_3951_);
    return v_res_3953_;
}
pub unsafe fn l_Std_Time_DateTime_weekday___redArg(
    mut v_dt_3954_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: u8 = 0;
    v_date_3955_ = crate::leanh::lean_ctor_get(v_dt_3954_, 1);
    v___x_3956_ = lean_thunk_get_own(v_date_3955_);
    v_date_3957_ = crate::leanh::lean_ctor_get(v___x_3956_, 0);
    crate::leanh::lean_inc_ref(v_date_3957_);
    crate::leanh::lean_dec(v___x_3956_);
    v___x_3958_ = l_Std_Time_PlainDate_weekday(v_date_3957_);
    return v___x_3958_;
}
pub unsafe fn l_Std_Time_DateTime_weekday___redArg___boxed(
    mut v_dt_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3960_: u8 = 0;
    let mut v_r_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3960_ = l_Std_Time_DateTime_weekday___redArg(v_dt_3959_);
    crate::leanh::lean_dec_ref(v_dt_3959_);
    v_r_3961_ = crate::leanh::lean_box((v_res_3960_) as usize);
    return v_r_3961_;
}
pub unsafe fn l_Std_Time_DateTime_weekday(
    mut v_tz_3962_: *mut crate::leanh::LeanObject,
    mut v_dt_3963_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: u8 = 0;
    v_date_3964_ = crate::leanh::lean_ctor_get(v_dt_3963_, 1);
    v___x_3965_ = lean_thunk_get_own(v_date_3964_);
    v_date_3966_ = crate::leanh::lean_ctor_get(v___x_3965_, 0);
    crate::leanh::lean_inc_ref(v_date_3966_);
    crate::leanh::lean_dec(v___x_3965_);
    v___x_3967_ = l_Std_Time_PlainDate_weekday(v_date_3966_);
    return v___x_3967_;
}
pub unsafe fn l_Std_Time_DateTime_weekday___boxed(
    mut v_tz_3968_: *mut crate::leanh::LeanObject,
    mut v_dt_3969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3970_: u8 = 0;
    let mut v_r_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3970_ = l_Std_Time_DateTime_weekday(v_tz_3968_, v_dt_3969_);
    crate::leanh::lean_dec_ref(v_dt_3969_);
    crate::leanh::lean_dec_ref(v_tz_3968_);
    v_r_3971_ = crate::leanh::lean_box((v_res_3970_) as usize);
    return v_r_3971_;
}
pub unsafe fn l_Std_Time_DateTime_era___redArg(
    mut v_date_3972_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    v_date_3973_ = crate::leanh::lean_ctor_get(v_date_3972_, 1);
    v___x_3974_ = lean_thunk_get_own(v_date_3973_);
    v_date_3975_ = crate::leanh::lean_ctor_get(v___x_3974_, 0);
    crate::leanh::lean_inc_ref(v_date_3975_);
    crate::leanh::lean_dec(v___x_3974_);
    v_year_3976_ = crate::leanh::lean_ctor_get(v_date_3975_, 0);
    crate::leanh::lean_inc(v_year_3976_);
    crate::leanh::lean_dec_ref(v_date_3975_);
    v___x_3977_ = l_Std_Time_Year_Offset_era(v_year_3976_);
    crate::leanh::lean_dec(v_year_3976_);
    return v___x_3977_;
}
pub unsafe fn l_Std_Time_DateTime_era___redArg___boxed(
    mut v_date_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3979_: u8 = 0;
    let mut v_r_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Std_Time_DateTime_era___redArg(v_date_3978_);
    crate::leanh::lean_dec_ref(v_date_3978_);
    v_r_3980_ = crate::leanh::lean_box((v_res_3979_) as usize);
    return v_r_3980_;
}
pub unsafe fn l_Std_Time_DateTime_era(
    mut v_tz_3981_: *mut crate::leanh::LeanObject,
    mut v_date_3982_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3983_: u8 = 0;
    v___x_3983_ = l_Std_Time_DateTime_era___redArg(v_date_3982_);
    return v___x_3983_;
}
pub unsafe fn l_Std_Time_DateTime_era___boxed(
    mut v_tz_3984_: *mut crate::leanh::LeanObject,
    mut v_date_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3986_: u8 = 0;
    let mut v_r_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_Std_Time_DateTime_era(v_tz_3984_, v_date_3985_);
    crate::leanh::lean_dec_ref(v_date_3985_);
    crate::leanh::lean_dec_ref(v_tz_3984_);
    v_r_3987_ = crate::leanh::lean_box((v_res_3986_) as usize);
    return v_r_3987_;
}
pub unsafe fn l_Std_Time_DateTime_withWeekday(
    mut v_tz_3988_: *mut crate::leanh::LeanObject,
    mut v_dt_3989_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_3990_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3994_: u8 = 0;
    let mut v_offset_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4015_: u8 = 0;
    let mut v_unused_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_3991_ = crate::leanh::lean_ctor_get(v_dt_3989_, 1);
                v_isSharedCheck_4015_ = (!crate::leanh::lean_is_exclusive(v_dt_3989_)) as u8;
                if v_isSharedCheck_4015_ == 0 {
                    v_unused_4016_ = crate::leanh::lean_ctor_get(v_dt_3989_, 0);
                    crate::leanh::lean_dec(v_unused_4016_);
                    v___x_3993_ = v_dt_3989_;
                    v_isShared_3994_ = v_isSharedCheck_4015_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_3991_);
                    crate::leanh::lean_dec(v_dt_3989_);
                    v___x_3993_ = crate::leanh::lean_box(0);
                    v_isShared_3994_ = v_isSharedCheck_4015_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_offset_3995_ = crate::leanh::lean_ctor_get(v_tz_3988_, 0);
                v___x_3996_ = lean_thunk_get_own(v_date_3991_);
                crate::leanh::lean_dec_ref(v_date_3991_);
                v___x_3997_ =
                    l_Std_Time_PlainDateTime_withWeekday(v___x_3996_, v_desiredWeekday_3990_);
                crate::leanh::lean_inc_ref(v___x_3997_);
                v___x_3998_ = l_Std_Time_PlainDateTime_toWallTime(v___x_3997_);
                v_second_3999_ = crate::leanh::lean_ctor_get(v___x_3998_, 0);
                crate::leanh::lean_inc(v_second_3999_);
                v_nano_4000_ = crate::leanh::lean_ctor_get(v___x_3998_, 1);
                crate::leanh::lean_inc(v_nano_4000_);
                crate::leanh::lean_dec_ref(v___x_3998_);
                v___f_4001_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4001_, 0, v___x_3997_);
                v___x_4002_ = lean_int_neg(v_offset_3995_);
                v___x_4003_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_4004_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4005_ = lean_int_mul(v_second_3999_, v___x_4004_);
                crate::leanh::lean_dec(v_second_3999_);
                v___x_4006_ = lean_int_add(v___x_4005_, v_nano_4000_);
                crate::leanh::lean_dec(v_nano_4000_);
                crate::leanh::lean_dec(v___x_4005_);
                v___x_4007_ = lean_int_mul(v___x_4002_, v___x_4004_);
                crate::leanh::lean_dec(v___x_4002_);
                v___x_4008_ = lean_int_add(v___x_4007_, v___x_4003_);
                crate::leanh::lean_dec(v___x_4007_);
                v___x_4009_ = lean_int_add(v___x_4006_, v___x_4008_);
                crate::leanh::lean_dec(v___x_4008_);
                crate::leanh::lean_dec(v___x_4006_);
                v_tm_4010_ = l_Std_Time_Duration_ofNanoseconds(v___x_4009_);
                crate::leanh::lean_dec(v___x_4009_);
                v___x_4011_ = lean_mk_thunk(v___f_4001_);
                if v_isShared_3994_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3993_, 1, v___x_4011_);
                    crate::leanh::lean_ctor_set(v___x_3993_, 0, v_tm_4010_);
                    v___x_4013_ = v___x_3993_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4014_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4014_, 0, v_tm_4010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4014_, 1, v___x_4011_);
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
    mut v_tz_4017_: *mut crate::leanh::LeanObject,
    mut v_dt_4018_: *mut crate::leanh::LeanObject,
    mut v_desiredWeekday_4019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_desiredWeekday_boxed_4020_: u8 = 0;
    let mut v_res_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_desiredWeekday_boxed_4020_ = (crate::leanh::lean_unbox(v_desiredWeekday_4019_) as u8);
    v_res_4021_ =
        l_Std_Time_DateTime_withWeekday(v_tz_4017_, v_dt_4018_, v_desiredWeekday_boxed_4020_);
    crate::leanh::lean_dec_ref(v_tz_4017_);
    return v_res_4021_;
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear___redArg(
    mut v_date_4022_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_date_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4023_ = crate::leanh::lean_ctor_get(v_date_4022_, 1);
                v___x_4024_ = lean_thunk_get_own(v_date_4023_);
                v_date_4025_ = crate::leanh::lean_ctor_get(v___x_4024_, 0);
                crate::leanh::lean_inc_ref(v_date_4025_);
                crate::leanh::lean_dec(v___x_4024_);
                v_year_4026_ = crate::leanh::lean_ctor_get(v_date_4025_, 0);
                crate::leanh::lean_inc(v_year_4026_);
                crate::leanh::lean_dec_ref(v_date_4025_);
                v___x_4027_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_4028_ = lean_int_mod(v_year_4026_, v___x_4027_);
                v___x_4029_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_4034_ = lean_int_dec_eq(v___x_4028_, v___x_4029_);
                crate::leanh::lean_dec(v___x_4028_);
                if v___x_4034_ == 0 {
                    crate::leanh::lean_dec(v_year_4026_);
                    return v___x_4034_;
                } else {
                    v___x_4035_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_4036_ = lean_int_mod(v_year_4026_, v___x_4035_);
                    v___x_4037_ = lean_int_dec_eq(v___x_4036_, v___x_4029_);
                    crate::leanh::lean_dec(v___x_4036_);
                    if v___x_4037_ == 0 {
                        if v___x_4034_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_year_4026_);
                            return v___x_4034_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4031_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_4032_ = lean_int_mod(v_year_4026_, v___x_4031_);
                crate::leanh::lean_dec(v_year_4026_);
                v___x_4033_ = lean_int_dec_eq(v___x_4032_, v___x_4029_);
                crate::leanh::lean_dec(v___x_4032_);
                return v___x_4033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear___redArg___boxed(
    mut v_date_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4039_: u8 = 0;
    let mut v_r_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_4038_);
    crate::leanh::lean_dec_ref(v_date_4038_);
    v_r_4040_ = crate::leanh::lean_box((v_res_4039_) as usize);
    return v_r_4040_;
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear(
    mut v_tz_4041_: *mut crate::leanh::LeanObject,
    mut v_date_4042_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4043_: u8 = 0;
    v___x_4043_ = l_Std_Time_DateTime_inLeapYear___redArg(v_date_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Std_Time_DateTime_inLeapYear___boxed(
    mut v_tz_4044_: *mut crate::leanh::LeanObject,
    mut v_date_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4046_: u8 = 0;
    let mut v_r_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4046_ = l_Std_Time_DateTime_inLeapYear(v_tz_4044_, v_date_4045_);
    crate::leanh::lean_dec_ref(v_date_4045_);
    crate::leanh::lean_dec_ref(v_tz_4044_);
    v_r_4047_ = crate::leanh::lean_box((v_res_4046_) as usize);
    return v_r_4047_;
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear___redArg(
    mut v_date_4048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4051_: u8 = 0;
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4056_: u8 = 0;
    let mut v_month_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_day_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4063_: u8 = 0;
    let mut v_unused_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_year_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: u8 = 0;
    let mut v___x_4075_: u8 = 0;
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_date_4049_ = crate::leanh::lean_ctor_get(v_date_4048_, 1);
                v___x_4065_ = lean_thunk_get_own(v_date_4049_);
                v_date_4066_ = crate::leanh::lean_ctor_get(v___x_4065_, 0);
                crate::leanh::lean_inc_ref(v_date_4066_);
                crate::leanh::lean_dec(v___x_4065_);
                v_year_4067_ = crate::leanh::lean_ctor_get(v_date_4066_, 0);
                crate::leanh::lean_inc(v_year_4067_);
                crate::leanh::lean_dec_ref(v_date_4066_);
                v___x_4068_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__0_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__0,
                );
                v___x_4069_ = lean_int_mod(v_year_4067_, v___x_4068_);
                v___x_4070_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__0,
                );
                v___x_4075_ = lean_int_dec_eq(v___x_4069_, v___x_4070_);
                crate::leanh::lean_dec(v___x_4069_);
                if v___x_4075_ == 0 {
                    crate::leanh::lean_dec(v_year_4067_);
                    v___y_4051_ = v___x_4075_;
                    state = 1;
                    continue;
                } else {
                    v___x_4076_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2),
                        core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__2_once),
                        _init_l_Std_Time_DateTime_withDaysClip___closed__2,
                    );
                    v___x_4077_ = lean_int_mod(v_year_4067_, v___x_4076_);
                    v___x_4078_ = lean_int_dec_eq(v___x_4077_, v___x_4070_);
                    crate::leanh::lean_dec(v___x_4077_);
                    if v___x_4078_ == 0 {
                        if v___x_4075_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_year_4067_);
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
                v_date_4053_ = crate::leanh::lean_ctor_get(v___x_4052_, 0);
                v_isSharedCheck_4063_ = (!crate::leanh::lean_is_exclusive(v___x_4052_)) as u8;
                if v_isSharedCheck_4063_ == 0 {
                    v_unused_4064_ = crate::leanh::lean_ctor_get(v___x_4052_, 1);
                    crate::leanh::lean_dec(v_unused_4064_);
                    v___x_4055_ = v___x_4052_;
                    v_isShared_4056_ = v_isSharedCheck_4063_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_date_4053_);
                    crate::leanh::lean_dec(v___x_4052_);
                    v___x_4055_ = crate::leanh::lean_box(0);
                    v_isShared_4056_ = v_isSharedCheck_4063_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_month_4057_ = crate::leanh::lean_ctor_get(v_date_4053_, 1);
                crate::leanh::lean_inc(v_month_4057_);
                v_day_4058_ = crate::leanh::lean_ctor_get(v_date_4053_, 2);
                crate::leanh::lean_inc(v_day_4058_);
                crate::leanh::lean_dec_ref(v_date_4053_);
                if v_isShared_4056_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4055_, 1, v_day_4058_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 0, v_month_4057_);
                    v___x_4060_ = v___x_4055_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4062_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_month_4057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4062_, 1, v_day_4058_);
                    v___x_4060_ = v_reuseFailAlloc_4062_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4061_ = l_Std_Time_ValidDate_dayOfYear(v___y_4051_, v___x_4060_);
                crate::leanh::lean_dec_ref(v___x_4060_);
                return v___x_4061_;
            }
            4 => {
                v___x_4072_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_withDaysClip___closed__1_once),
                    _init_l_Std_Time_DateTime_withDaysClip___closed__1,
                );
                v___x_4073_ = lean_int_mod(v_year_4067_, v___x_4072_);
                crate::leanh::lean_dec(v_year_4067_);
                v___x_4074_ = lean_int_dec_eq(v___x_4073_, v___x_4070_);
                crate::leanh::lean_dec(v___x_4073_);
                v___y_4051_ = v___x_4074_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear___redArg___boxed(
    mut v_date_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_4079_);
    crate::leanh::lean_dec_ref(v_date_4079_);
    return v_res_4080_;
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear(
    mut v_tz_4081_: *mut crate::leanh::LeanObject,
    mut v_date_4082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4083_ = l_Std_Time_DateTime_dayOfYear___redArg(v_date_4082_);
    return v___x_4083_;
}
pub unsafe fn l_Std_Time_DateTime_dayOfYear___boxed(
    mut v_tz_4084_: *mut crate::leanh::LeanObject,
    mut v_date_4085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4086_ = l_Std_Time_DateTime_dayOfYear(v_tz_4084_, v_date_4085_);
    crate::leanh::lean_dec_ref(v_date_4085_);
    crate::leanh::lean_dec_ref(v_tz_4084_);
    return v_res_4086_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear___redArg(
    mut v_date_4087_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4088_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4089_ = crate::leanh::lean_ctor_get(v_date_4087_, 1);
    v___x_4090_ = lean_thunk_get_own(v_date_4089_);
    v_date_4091_ = crate::leanh::lean_ctor_get(v___x_4090_, 0);
    crate::leanh::lean_inc_ref(v_date_4091_);
    crate::leanh::lean_dec(v___x_4090_);
    v___x_4092_ = l_Std_Time_PlainDate_weekOfYear(v_date_4091_, v_firstDay_4088_);
    return v___x_4092_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear___redArg___boxed(
    mut v_date_4093_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_4095_: u8 = 0;
    let mut v_res_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4095_ = (crate::leanh::lean_unbox(v_firstDay_4094_) as u8);
    v_res_4096_ = l_Std_Time_DateTime_weekOfYear___redArg(v_date_4093_, v_firstDay_boxed_4095_);
    crate::leanh::lean_dec_ref(v_date_4093_);
    return v_res_4096_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear(
    mut v_tz_4097_: *mut crate::leanh::LeanObject,
    mut v_date_4098_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4099_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4100_ = crate::leanh::lean_ctor_get(v_date_4098_, 1);
    v___x_4101_ = lean_thunk_get_own(v_date_4100_);
    v_date_4102_ = crate::leanh::lean_ctor_get(v___x_4101_, 0);
    crate::leanh::lean_inc_ref(v_date_4102_);
    crate::leanh::lean_dec(v___x_4101_);
    v___x_4103_ = l_Std_Time_PlainDate_weekOfYear(v_date_4102_, v_firstDay_4099_);
    return v___x_4103_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfYear___boxed(
    mut v_tz_4104_: *mut crate::leanh::LeanObject,
    mut v_date_4105_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_4107_: u8 = 0;
    let mut v_res_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4107_ = (crate::leanh::lean_unbox(v_firstDay_4106_) as u8);
    v_res_4108_ = l_Std_Time_DateTime_weekOfYear(v_tz_4104_, v_date_4105_, v_firstDay_boxed_4107_);
    crate::leanh::lean_dec_ref(v_date_4105_);
    crate::leanh::lean_dec_ref(v_tz_4104_);
    return v_res_4108_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear___redArg(
    mut v_date_4109_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4110_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4111_ = crate::leanh::lean_ctor_get(v_date_4109_, 1);
    v___x_4112_ = lean_thunk_get_own(v_date_4111_);
    v_date_4113_ = crate::leanh::lean_ctor_get(v___x_4112_, 0);
    crate::leanh::lean_inc_ref(v_date_4113_);
    crate::leanh::lean_dec(v___x_4112_);
    v___x_4114_ = l_Std_Time_PlainDate_weekYear(v_date_4113_, v_firstDay_4110_);
    return v___x_4114_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear___redArg___boxed(
    mut v_date_4115_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_4117_: u8 = 0;
    let mut v_res_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4117_ = (crate::leanh::lean_unbox(v_firstDay_4116_) as u8);
    v_res_4118_ = l_Std_Time_DateTime_weekYear___redArg(v_date_4115_, v_firstDay_boxed_4117_);
    crate::leanh::lean_dec_ref(v_date_4115_);
    return v_res_4118_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear(
    mut v_tz_4119_: *mut crate::leanh::LeanObject,
    mut v_date_4120_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4121_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4122_ = crate::leanh::lean_ctor_get(v_date_4120_, 1);
    v___x_4123_ = lean_thunk_get_own(v_date_4122_);
    v_date_4124_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
    crate::leanh::lean_inc_ref(v_date_4124_);
    crate::leanh::lean_dec(v___x_4123_);
    v___x_4125_ = l_Std_Time_PlainDate_weekYear(v_date_4124_, v_firstDay_4121_);
    return v___x_4125_;
}
pub unsafe fn l_Std_Time_DateTime_weekYear___boxed(
    mut v_tz_4126_: *mut crate::leanh::LeanObject,
    mut v_date_4127_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_4129_: u8 = 0;
    let mut v_res_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4129_ = (crate::leanh::lean_unbox(v_firstDay_4128_) as u8);
    v_res_4130_ = l_Std_Time_DateTime_weekYear(v_tz_4126_, v_date_4127_, v_firstDay_boxed_4129_);
    crate::leanh::lean_dec_ref(v_date_4127_);
    crate::leanh::lean_dec_ref(v_tz_4126_);
    return v_res_4130_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth___redArg(
    mut v_date_4131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4132_ = crate::leanh::lean_ctor_get(v_date_4131_, 1);
    v___x_4133_ = lean_thunk_get_own(v_date_4132_);
    v___x_4134_ = l_Std_Time_PlainDateTime_weekOfMonth(v___x_4133_);
    crate::leanh::lean_dec(v___x_4133_);
    return v___x_4134_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth___redArg___boxed(
    mut v_date_4135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4136_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_4135_);
    crate::leanh::lean_dec_ref(v_date_4135_);
    return v_res_4136_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth(
    mut v_tz_4137_: *mut crate::leanh::LeanObject,
    mut v_date_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4139_ = l_Std_Time_DateTime_weekOfMonth___redArg(v_date_4138_);
    return v___x_4139_;
}
pub unsafe fn l_Std_Time_DateTime_weekOfMonth___boxed(
    mut v_tz_4140_: *mut crate::leanh::LeanObject,
    mut v_date_4141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4142_ = l_Std_Time_DateTime_weekOfMonth(v_tz_4140_, v_date_4141_);
    crate::leanh::lean_dec_ref(v_date_4141_);
    crate::leanh::lean_dec_ref(v_tz_4140_);
    return v_res_4142_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth___redArg(
    mut v_date_4143_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4144_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4145_ = crate::leanh::lean_ctor_get(v_date_4143_, 1);
    v___x_4146_ = lean_thunk_get_own(v_date_4145_);
    v_date_4147_ = crate::leanh::lean_ctor_get(v___x_4146_, 0);
    crate::leanh::lean_inc_ref(v_date_4147_);
    crate::leanh::lean_dec(v___x_4146_);
    v___x_4148_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_4147_, v_firstDay_4144_);
    return v___x_4148_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth___redArg___boxed(
    mut v_date_4149_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_4151_: u8 = 0;
    let mut v_res_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4151_ = (crate::leanh::lean_unbox(v_firstDay_4150_) as u8);
    v_res_4152_ =
        l_Std_Time_DateTime_alignedWeekOfMonth___redArg(v_date_4149_, v_firstDay_boxed_4151_);
    crate::leanh::lean_dec_ref(v_date_4149_);
    return v_res_4152_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth(
    mut v_tz_4153_: *mut crate::leanh::LeanObject,
    mut v_date_4154_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4155_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4156_ = crate::leanh::lean_ctor_get(v_date_4154_, 1);
    v___x_4157_ = lean_thunk_get_own(v_date_4156_);
    v_date_4158_ = crate::leanh::lean_ctor_get(v___x_4157_, 0);
    crate::leanh::lean_inc_ref(v_date_4158_);
    crate::leanh::lean_dec(v___x_4157_);
    v___x_4159_ = l_Std_Time_PlainDate_alignedWeekOfMonth(v_date_4158_, v_firstDay_4155_);
    return v___x_4159_;
}
pub unsafe fn l_Std_Time_DateTime_alignedWeekOfMonth___boxed(
    mut v_tz_4160_: *mut crate::leanh::LeanObject,
    mut v_date_4161_: *mut crate::leanh::LeanObject,
    mut v_firstDay_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstDay_boxed_4163_: u8 = 0;
    let mut v_res_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstDay_boxed_4163_ = (crate::leanh::lean_unbox(v_firstDay_4162_) as u8);
    v_res_4164_ =
        l_Std_Time_DateTime_alignedWeekOfMonth(v_tz_4160_, v_date_4161_, v_firstDay_boxed_4163_);
    crate::leanh::lean_dec_ref(v_date_4161_);
    crate::leanh::lean_dec_ref(v_tz_4160_);
    return v_res_4164_;
}
pub unsafe fn l_Std_Time_DateTime_quarter___redArg(
    mut v_date_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4166_ = crate::leanh::lean_ctor_get(v_date_4165_, 1);
    v___x_4167_ = lean_thunk_get_own(v_date_4166_);
    v_date_4168_ = crate::leanh::lean_ctor_get(v___x_4167_, 0);
    crate::leanh::lean_inc_ref(v_date_4168_);
    crate::leanh::lean_dec(v___x_4167_);
    v___x_4169_ = l_Std_Time_PlainDate_quarter(v_date_4168_);
    crate::leanh::lean_dec_ref(v_date_4168_);
    return v___x_4169_;
}
pub unsafe fn l_Std_Time_DateTime_quarter___redArg___boxed(
    mut v_date_4170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4171_ = l_Std_Time_DateTime_quarter___redArg(v_date_4170_);
    crate::leanh::lean_dec_ref(v_date_4170_);
    return v_res_4171_;
}
pub unsafe fn l_Std_Time_DateTime_quarter(
    mut v_tz_4172_: *mut crate::leanh::LeanObject,
    mut v_date_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_date_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4174_ = crate::leanh::lean_ctor_get(v_date_4173_, 1);
    v___x_4175_ = lean_thunk_get_own(v_date_4174_);
    v_date_4176_ = crate::leanh::lean_ctor_get(v___x_4175_, 0);
    crate::leanh::lean_inc_ref(v_date_4176_);
    crate::leanh::lean_dec(v___x_4175_);
    v___x_4177_ = l_Std_Time_PlainDate_quarter(v_date_4176_);
    crate::leanh::lean_dec_ref(v_date_4176_);
    return v___x_4177_;
}
pub unsafe fn l_Std_Time_DateTime_quarter___boxed(
    mut v_tz_4178_: *mut crate::leanh::LeanObject,
    mut v_date_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Std_Time_DateTime_quarter(v_tz_4178_, v_date_4179_);
    crate::leanh::lean_dec_ref(v_date_4179_);
    crate::leanh::lean_dec_ref(v_tz_4178_);
    return v_res_4180_;
}
pub unsafe fn l_Std_Time_DateTime_time___redArg(
    mut v_zdt_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4182_ = crate::leanh::lean_ctor_get(v_zdt_4181_, 1);
    v___x_4183_ = lean_thunk_get_own(v_date_4182_);
    v_time_4184_ = crate::leanh::lean_ctor_get(v___x_4183_, 1);
    crate::leanh::lean_inc_ref(v_time_4184_);
    crate::leanh::lean_dec(v___x_4183_);
    return v_time_4184_;
}
pub unsafe fn l_Std_Time_DateTime_time___redArg___boxed(
    mut v_zdt_4185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4186_ = l_Std_Time_DateTime_time___redArg(v_zdt_4185_);
    crate::leanh::lean_dec_ref(v_zdt_4185_);
    return v_res_4186_;
}
pub unsafe fn l_Std_Time_DateTime_time(
    mut v_tz_4187_: *mut crate::leanh::LeanObject,
    mut v_zdt_4188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_date_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_date_4189_ = crate::leanh::lean_ctor_get(v_zdt_4188_, 1);
    v___x_4190_ = lean_thunk_get_own(v_date_4189_);
    v_time_4191_ = crate::leanh::lean_ctor_get(v___x_4190_, 1);
    crate::leanh::lean_inc_ref(v_time_4191_);
    crate::leanh::lean_dec(v___x_4190_);
    return v_time_4191_;
}
pub unsafe fn l_Std_Time_DateTime_time___boxed(
    mut v_tz_4192_: *mut crate::leanh::LeanObject,
    mut v_zdt_4193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4194_ = l_Std_Time_DateTime_time(v_tz_4192_, v_zdt_4193_);
    crate::leanh::lean_dec_ref(v_zdt_4193_);
    crate::leanh::lean_dec_ref(v_tz_4192_);
    return v_res_4194_;
}
pub unsafe fn l_Std_Time_DateTime_ofEpochDay(
    mut v_days_4195_: *mut crate::leanh::LeanObject,
    mut v_time_4196_: *mut crate::leanh::LeanObject,
    mut v_tz_4197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_offset_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4206_: u8 = 0;
    let mut v___f_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tm_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_offset_4198_ = crate::leanh::lean_ctor_get(v_tz_4197_, 0);
                v___x_4199_ = l_Std_Time_PlainDate_ofEpochDay(v_days_4195_);
                v___x_4200_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4200_, 0, v___x_4199_);
                crate::leanh::lean_ctor_set(v___x_4200_, 1, v_time_4196_);
                crate::leanh::lean_inc_ref(v___x_4200_);
                v___x_4201_ = l_Std_Time_PlainDateTime_toWallTime(v___x_4200_);
                v_second_4202_ = crate::leanh::lean_ctor_get(v___x_4201_, 0);
                v_nano_4203_ = crate::leanh::lean_ctor_get(v___x_4201_, 1);
                v_isSharedCheck_4221_ = (!crate::leanh::lean_is_exclusive(v___x_4201_)) as u8;
                if v_isSharedCheck_4221_ == 0 {
                    v___x_4205_ = v___x_4201_;
                    v_isShared_4206_ = v_isSharedCheck_4221_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_nano_4203_);
                    crate::leanh::lean_inc(v_second_4202_);
                    crate::leanh::lean_dec(v___x_4201_);
                    v___x_4205_ = crate::leanh::lean_box(0);
                    v_isShared_4206_ = v_isSharedCheck_4221_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_4207_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMonthsClip___lam__0___boxed as *mut core::ffi::c_void,
                    2,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4207_, 0, v___x_4200_);
                v___x_4208_ = lean_int_neg(v_offset_4198_);
                v___x_4209_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofPlainDateTime___closed__0_once),
                    _init_l_Std_Time_DateTime_ofPlainDateTime___closed__0,
                );
                v___x_4210_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4211_ = lean_int_mul(v_second_4202_, v___x_4210_);
                crate::leanh::lean_dec(v_second_4202_);
                v___x_4212_ = lean_int_add(v___x_4211_, v_nano_4203_);
                crate::leanh::lean_dec(v_nano_4203_);
                crate::leanh::lean_dec(v___x_4211_);
                v___x_4213_ = lean_int_mul(v___x_4208_, v___x_4210_);
                crate::leanh::lean_dec(v___x_4208_);
                v___x_4214_ = lean_int_add(v___x_4213_, v___x_4209_);
                crate::leanh::lean_dec(v___x_4213_);
                v___x_4215_ = lean_int_add(v___x_4212_, v___x_4214_);
                crate::leanh::lean_dec(v___x_4214_);
                crate::leanh::lean_dec(v___x_4212_);
                v_tm_4216_ = l_Std_Time_Duration_ofNanoseconds(v___x_4215_);
                crate::leanh::lean_dec(v___x_4215_);
                v___x_4217_ = lean_mk_thunk(v___f_4207_);
                if v_isShared_4206_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4205_, 1, v___x_4217_);
                    crate::leanh::lean_ctor_set(v___x_4205_, 0, v_tm_4216_);
                    v___x_4219_ = v___x_4205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_tm_4216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4217_);
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
    mut v_days_4222_: *mut crate::leanh::LeanObject,
    mut v_time_4223_: *mut crate::leanh::LeanObject,
    mut v_tz_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Std_Time_DateTime_ofEpochDay(v_days_4222_, v_time_4223_, v_tz_4224_);
    crate::leanh::lean_dec_ref(v_tz_4224_);
    crate::leanh::lean_dec(v_days_4222_);
    return v_res_4225_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset(
    mut v_tz_4226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4227_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_addDays___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4227_, 0, v_tz_4226_);
    return v___x_4227_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset(
    mut v_tz_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4229_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_subDays___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4229_, 0, v_tz_4228_);
    return v___x_4229_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__1(
    mut v_tz_4230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4231_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_addWeeks___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4231_, 0, v_tz_4230_);
    return v___x_4231_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__1(
    mut v_tz_4232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_subWeeks___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4233_, 0, v_tz_4232_);
    return v___x_4233_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__2(
    mut v_tz_4234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4235_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_addHours___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4235_, 0, v_tz_4234_);
    return v___x_4235_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__2(
    mut v_tz_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4237_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_subHours___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4237_, 0, v_tz_4236_);
    return v___x_4237_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__3(
    mut v_tz_4238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4239_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_addMinutes___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4239_, 0, v_tz_4238_);
    return v___x_4239_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__3(
    mut v_tz_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4241_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_subMinutes___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4241_, 0, v_tz_4240_);
    return v___x_4241_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__4(
    mut v_tz_4242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4243_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_addSeconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4243_, 0, v_tz_4242_);
    return v___x_4243_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__4(
    mut v_tz_4244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4245_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_subSeconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4245_, 0, v_tz_4244_);
    return v___x_4245_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__5(
    mut v_tz_4246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_addMilliseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4247_, 0, v_tz_4246_);
    return v___x_4247_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__5(
    mut v_tz_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4249_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_subMilliseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4249_, 0, v_tz_4248_);
    return v___x_4249_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddOffset__6(
    mut v_tz_4250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_addNanoseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4251_, 0, v_tz_4250_);
    return v___x_4251_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubOffset__6(
    mut v_tz_4252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4253_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_subNanoseconds___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_4253_, 0, v_tz_4252_);
    return v___x_4253_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration___lam__0(
    mut v_x_4254_: *mut crate::leanh::LeanObject,
    mut v_y_4255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timestamp_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_timestamp_4256_ = crate::leanh::lean_ctor_get(v_y_4255_, 0);
    v_timestamp_4257_ = crate::leanh::lean_ctor_get(v_x_4254_, 0);
    v_second_4258_ = crate::leanh::lean_ctor_get(v_timestamp_4256_, 0);
    v_nano_4259_ = crate::leanh::lean_ctor_get(v_timestamp_4256_, 1);
    v_second_4260_ = crate::leanh::lean_ctor_get(v_timestamp_4257_, 0);
    v_nano_4261_ = crate::leanh::lean_ctor_get(v_timestamp_4257_, 1);
    v___x_4262_ = lean_int_neg(v_second_4258_);
    v___x_4263_ = lean_int_neg(v_nano_4259_);
    v___x_4264_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once),
        _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
    );
    v___x_4265_ = lean_int_mul(v_second_4260_, v___x_4264_);
    v___x_4266_ = lean_int_add(v___x_4265_, v_nano_4261_);
    crate::leanh::lean_dec(v___x_4265_);
    v___x_4267_ = lean_int_mul(v___x_4262_, v___x_4264_);
    crate::leanh::lean_dec(v___x_4262_);
    v___x_4268_ = lean_int_add(v___x_4267_, v___x_4263_);
    crate::leanh::lean_dec(v___x_4263_);
    crate::leanh::lean_dec(v___x_4267_);
    v___x_4269_ = lean_int_add(v___x_4266_, v___x_4268_);
    crate::leanh::lean_dec(v___x_4268_);
    crate::leanh::lean_dec(v___x_4266_);
    v___x_4270_ = l_Std_Time_Duration_ofNanoseconds(v___x_4269_);
    crate::leanh::lean_dec(v___x_4269_);
    return v___x_4270_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration___lam__0___boxed(
    mut v_x_4271_: *mut crate::leanh::LeanObject,
    mut v_y_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4273_ = l_Std_Time_DateTime_instHSubDuration___lam__0(v_x_4271_, v_y_4272_);
    crate::leanh::lean_dec_ref(v_y_4272_);
    crate::leanh::lean_dec_ref(v_x_4271_);
    return v_res_4273_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration(
    mut v_tz_4275_: *mut crate::leanh::LeanObject,
    mut v_tz_u2081_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4277_ = l_Std_Time_DateTime_instHSubDuration___closed__0;
    return v___f_4277_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration___boxed(
    mut v_tz_4278_: *mut crate::leanh::LeanObject,
    mut v_tz_u2081_4279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4280_ = l_Std_Time_DateTime_instHSubDuration(v_tz_4278_, v_tz_u2081_4279_);
    crate::leanh::lean_dec_ref(v_tz_u2081_4279_);
    crate::leanh::lean_dec_ref(v_tz_4278_);
    return v_res_4280_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddDuration___lam__1(
    mut v_tz_4281_: *mut crate::leanh::LeanObject,
    mut v_x_4282_: *mut crate::leanh::LeanObject,
    mut v_y_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_timestamp_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v_second_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4309_: u8 = 0;
    let mut v_unused_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_timestamp_4284_ = crate::leanh::lean_ctor_get(v_x_4282_, 0);
                v_isSharedCheck_4309_ = (!crate::leanh::lean_is_exclusive(v_x_4282_)) as u8;
                if v_isSharedCheck_4309_ == 0 {
                    v_unused_4310_ = crate::leanh::lean_ctor_get(v_x_4282_, 1);
                    crate::leanh::lean_dec(v_unused_4310_);
                    v___x_4286_ = v_x_4282_;
                    v_isShared_4287_ = v_isSharedCheck_4309_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_4284_);
                    crate::leanh::lean_dec(v_x_4282_);
                    v___x_4286_ = crate::leanh::lean_box(0);
                    v_isShared_4287_ = v_isSharedCheck_4309_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_second_4288_ = crate::leanh::lean_ctor_get(v_y_4283_, 0);
                v_nano_4289_ = crate::leanh::lean_ctor_get(v_y_4283_, 1);
                v_second_4290_ = crate::leanh::lean_ctor_get(v_timestamp_4284_, 0);
                crate::leanh::lean_inc(v_second_4290_);
                v_nano_4291_ = crate::leanh::lean_ctor_get(v_timestamp_4284_, 1);
                crate::leanh::lean_inc(v_nano_4291_);
                crate::leanh::lean_dec_ref(v_timestamp_4284_);
                v___x_4292_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4293_ = lean_int_mul(v_second_4288_, v___x_4292_);
                v_nanos_4294_ = lean_int_add(v___x_4293_, v_nano_4289_);
                crate::leanh::lean_dec(v___x_4293_);
                v___x_4295_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_4294_);
                crate::leanh::lean_dec(v_nanos_4294_);
                v_second_4296_ = crate::leanh::lean_ctor_get(v___x_4295_, 0);
                crate::leanh::lean_inc(v_second_4296_);
                v_nano_4297_ = crate::leanh::lean_ctor_get(v___x_4295_, 1);
                crate::leanh::lean_inc(v_nano_4297_);
                crate::leanh::lean_dec_ref(v___x_4295_);
                v___x_4298_ = lean_int_mul(v_second_4290_, v___x_4292_);
                crate::leanh::lean_dec(v_second_4290_);
                v___x_4299_ = lean_int_add(v___x_4298_, v_nano_4291_);
                crate::leanh::lean_dec(v_nano_4291_);
                crate::leanh::lean_dec(v___x_4298_);
                v___x_4300_ = lean_int_mul(v_second_4296_, v___x_4292_);
                crate::leanh::lean_dec(v_second_4296_);
                v___x_4301_ = lean_int_add(v___x_4300_, v_nano_4297_);
                crate::leanh::lean_dec(v_nano_4297_);
                crate::leanh::lean_dec(v___x_4300_);
                v___x_4302_ = lean_int_add(v___x_4299_, v___x_4301_);
                crate::leanh::lean_dec(v___x_4301_);
                crate::leanh::lean_dec(v___x_4299_);
                v___x_4303_ = l_Std_Time_Duration_ofNanoseconds(v___x_4302_);
                crate::leanh::lean_dec(v___x_4302_);
                crate::leanh::lean_inc_ref(v___x_4303_);
                v___f_4304_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4304_, 0, v_tz_4281_);
                crate::leanh::lean_closure_set(v___f_4304_, 1, v___x_4303_);
                crate::leanh::lean_closure_set(v___f_4304_, 2, v___x_4292_);
                v___x_4305_ = lean_mk_thunk(v___f_4304_);
                if v_isShared_4287_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4286_, 1, v___x_4305_);
                    crate::leanh::lean_ctor_set(v___x_4286_, 0, v___x_4303_);
                    v___x_4307_ = v___x_4286_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4308_, 1, v___x_4305_);
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
    mut v_tz_4311_: *mut crate::leanh::LeanObject,
    mut v_x_4312_: *mut crate::leanh::LeanObject,
    mut v_y_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_Std_Time_DateTime_instHAddDuration___lam__1(v_tz_4311_, v_x_4312_, v_y_4313_);
    crate::leanh::lean_dec_ref(v_y_4313_);
    return v_res_4314_;
}
pub unsafe fn l_Std_Time_DateTime_instHAddDuration(
    mut v_tz_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4316_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_instHAddDuration___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4316_, 0, v_tz_4315_);
    return v___f_4316_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration__1___lam__1(
    mut v_tz_4317_: *mut crate::leanh::LeanObject,
    mut v_x_4318_: *mut crate::leanh::LeanObject,
    mut v_y_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_second_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_timestamp_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4325_: u8 = 0;
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nanos_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_second_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nano_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_unused_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_second_4320_ = crate::leanh::lean_ctor_get(v_y_4319_, 0);
                v_nano_4321_ = crate::leanh::lean_ctor_get(v_y_4319_, 1);
                v_timestamp_4322_ = crate::leanh::lean_ctor_get(v_x_4318_, 0);
                v_isSharedCheck_4347_ = (!crate::leanh::lean_is_exclusive(v_x_4318_)) as u8;
                if v_isSharedCheck_4347_ == 0 {
                    v_unused_4348_ = crate::leanh::lean_ctor_get(v_x_4318_, 1);
                    crate::leanh::lean_dec(v_unused_4348_);
                    v___x_4324_ = v_x_4318_;
                    v_isShared_4325_ = v_isSharedCheck_4347_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_timestamp_4322_);
                    crate::leanh::lean_dec(v_x_4318_);
                    v___x_4324_ = crate::leanh::lean_box(0);
                    v_isShared_4325_ = v_isSharedCheck_4347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4326_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1_once
                    ),
                    _init_l_Std_Time_DateTime_ofTimestamp___lam__0___closed__1,
                );
                v___x_4327_ = lean_int_mul(v_second_4320_, v___x_4326_);
                v_nanos_4328_ = lean_int_add(v___x_4327_, v_nano_4321_);
                crate::leanh::lean_dec(v___x_4327_);
                v___x_4329_ = l_Std_Time_Duration_ofNanoseconds(v_nanos_4328_);
                crate::leanh::lean_dec(v_nanos_4328_);
                v_second_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
                crate::leanh::lean_inc(v_second_4330_);
                v_nano_4331_ = crate::leanh::lean_ctor_get(v___x_4329_, 1);
                crate::leanh::lean_inc(v_nano_4331_);
                crate::leanh::lean_dec_ref(v___x_4329_);
                v_second_4332_ = crate::leanh::lean_ctor_get(v_timestamp_4322_, 0);
                crate::leanh::lean_inc(v_second_4332_);
                v_nano_4333_ = crate::leanh::lean_ctor_get(v_timestamp_4322_, 1);
                crate::leanh::lean_inc(v_nano_4333_);
                crate::leanh::lean_dec_ref(v_timestamp_4322_);
                v___x_4334_ = lean_int_neg(v_second_4330_);
                crate::leanh::lean_dec(v_second_4330_);
                v___x_4335_ = lean_int_neg(v_nano_4331_);
                crate::leanh::lean_dec(v_nano_4331_);
                v___x_4336_ = lean_int_mul(v_second_4332_, v___x_4326_);
                crate::leanh::lean_dec(v_second_4332_);
                v___x_4337_ = lean_int_add(v___x_4336_, v_nano_4333_);
                crate::leanh::lean_dec(v_nano_4333_);
                crate::leanh::lean_dec(v___x_4336_);
                v___x_4338_ = lean_int_mul(v___x_4334_, v___x_4326_);
                crate::leanh::lean_dec(v___x_4334_);
                v___x_4339_ = lean_int_add(v___x_4338_, v___x_4335_);
                crate::leanh::lean_dec(v___x_4335_);
                crate::leanh::lean_dec(v___x_4338_);
                v___x_4340_ = lean_int_add(v___x_4337_, v___x_4339_);
                crate::leanh::lean_dec(v___x_4339_);
                crate::leanh::lean_dec(v___x_4337_);
                v___x_4341_ = l_Std_Time_Duration_ofNanoseconds(v___x_4340_);
                crate::leanh::lean_dec(v___x_4340_);
                crate::leanh::lean_inc_ref(v___x_4341_);
                v___f_4342_ = crate::leanh::lean_alloc_closure(
                    l_Std_Time_DateTime_addMilliseconds___lam__0___boxed as *mut core::ffi::c_void,
                    4,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_4342_, 0, v_tz_4317_);
                crate::leanh::lean_closure_set(v___f_4342_, 1, v___x_4341_);
                crate::leanh::lean_closure_set(v___f_4342_, 2, v___x_4326_);
                v___x_4343_ = lean_mk_thunk(v___f_4342_);
                if v_isShared_4325_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4324_, 1, v___x_4343_);
                    crate::leanh::lean_ctor_set(v___x_4324_, 0, v___x_4341_);
                    v___x_4345_ = v___x_4324_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 1, v___x_4343_);
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
    mut v_tz_4349_: *mut crate::leanh::LeanObject,
    mut v_x_4350_: *mut crate::leanh::LeanObject,
    mut v_y_4351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4352_ =
        l_Std_Time_DateTime_instHSubDuration__1___lam__1(v_tz_4349_, v_x_4350_, v_y_4351_);
    crate::leanh::lean_dec_ref(v_y_4351_);
    return v_res_4352_;
}
pub unsafe fn l_Std_Time_DateTime_instHSubDuration__1(
    mut v_tz_4353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4354_ = crate::leanh::lean_alloc_closure(
        l_Std_Time_DateTime_instHSubDuration__1___lam__1___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_4354_, 0, v_tz_4353_);
    return v___f_4354_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_DateTime(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_TimeZone(builtin);
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
    res = runtime_initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_DateTime(
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
pub unsafe fn initialize_Std_Time_Zoned_DateTime(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_TimeZone(builtin);
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
    res = initialize_Std_Time_DateTime_PlainDateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_DateTime(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_DateTime(builtin);
}
