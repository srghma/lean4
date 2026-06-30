// Lean compiler output
// Module: Std.Time.Date.Unit.Basic
// Imports: Std.Time.Date.Unit.Year Std.Time.Date.Unit.Weekday Std.Time.Date.Unit.Week
use crate::ffi::{lean_int_ediv, lean_int_mul, lean_nat_to_int};
use crate::r#gen::Std::Time::Date::Unit::Week::{
    initialize_Std_Time_Date_Unit_Week, runtime_initialize_Std_Time_Date_Unit_Week,
};
use crate::r#gen::Std::Time::Date::Unit::Weekday::{
    initialize_Std_Time_Date_Unit_Weekday, runtime_initialize_Std_Time_Date_Unit_Weekday,
};
use crate::r#gen::Std::Time::Date::Unit::Year::{
    initialize_Std_Time_Date_Unit_Year, runtime_initialize_Std_Time_Date_Unit_Year,
};
static mut l_Std_Time_Day_Offset_ofWeeks___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Time_Day_Offset_ofWeeks___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Std_Time_Day_Offset_ofWeeks___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_13_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_14_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_13_ = leanh::lean_unsigned_to_nat(7);
    v___x_14_ = lean_nat_to_int(v___x_13_);
    return v___x_14_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofWeeks(
    mut v_week_15_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_16_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_16_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_ofWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_ofWeeks___closed__0_once),
        _init_l_Std_Time_Day_Offset_ofWeeks___closed__0,
    );
    v___x_17_ = lean_int_mul(v_week_15_, v___x_16_);
    return v___x_17_;
}
pub unsafe fn l_Std_Time_Day_Offset_ofWeeks___boxed(
    mut v_week_18_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_19_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_19_ = l_Std_Time_Day_Offset_ofWeeks(v_week_18_);
    leanh::lean_dec(v_week_18_);
    return v_res_19_;
}
pub unsafe fn l_Std_Time_Day_Offset_toWeeks(
    mut v_day_20_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_21_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_22_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_21_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_ofWeeks___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Day_Offset_ofWeeks___closed__0_once),
        _init_l_Std_Time_Day_Offset_ofWeeks___closed__0,
    );
    v___x_22_ = lean_int_ediv(v_day_20_, v___x_21_);
    return v___x_22_;
}
pub unsafe fn l_Std_Time_Day_Offset_toWeeks___boxed(
    mut v_day_23_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_24_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_24_ = l_Std_Time_Day_Offset_toWeeks(v_day_23_);
    leanh::lean_dec(v_day_23_);
    return v_res_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Date_Unit_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Date_Unit_Year(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Weekday(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Week(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Date_Unit_Basic(
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
pub unsafe fn initialize_Std_Time_Date_Unit_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Date_Unit_Year(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Weekday(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Date_Unit_Week(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Date_Unit_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Date_Unit_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Date_Unit_Basic(builtin);
}