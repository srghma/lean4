// Lean compiler output
// Module: Init.Grind.Offset
// Imports: Init.Grind.Tactics Init.Omega
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::ffi::{lean_nat_dec_le, lean_nat_dec_lt};
pub unsafe fn l_Lean_Grind_isLt(
    mut v_x_15_: *mut crate::leanh::LeanObject,
    mut v_y_16_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_17_: u8 = 0;
    v___x_17_ = lean_nat_dec_lt(v_x_15_, v_y_16_);
    return v___x_17_;
}
pub unsafe fn l_Lean_Grind_isLt___boxed(
    mut v_x_18_: *mut crate::leanh::LeanObject,
    mut v_y_19_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_20_: u8 = 0;
    let mut v_r_21_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_20_ = l_Lean_Grind_isLt(v_x_18_, v_y_19_);
    crate::leanh::lean_dec(v_y_19_);
    crate::leanh::lean_dec(v_x_18_);
    v_r_21_ = crate::leanh::lean_box((v_res_20_) as usize);
    return v_r_21_;
}
pub unsafe fn l_Lean_Grind_isLE(
    mut v_x_22_: *mut crate::leanh::LeanObject,
    mut v_y_23_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_24_: u8 = 0;
    v___x_24_ = lean_nat_dec_le(v_x_22_, v_y_23_);
    return v___x_24_;
}
pub unsafe fn l_Lean_Grind_isLE___boxed(
    mut v_x_25_: *mut crate::leanh::LeanObject,
    mut v_y_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_27_: u8 = 0;
    let mut v_r_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_27_ = l_Lean_Grind_isLE(v_x_25_, v_y_26_);
    crate::leanh::lean_dec(v_y_26_);
    crate::leanh::lean_dec(v_x_25_);
    v_r_28_ = crate::leanh::lean_box((v_res_27_) as usize);
    return v_r_28_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Offset(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Offset(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Offset(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Offset(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Offset(builtin);
}
