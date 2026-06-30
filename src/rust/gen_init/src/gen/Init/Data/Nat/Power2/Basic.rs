// Lean compiler output
// Module: Init.Data.Nat.Power2.Basic
// Imports: Init.Grind.Tactics Init.Data.Nat.Linear Init.NotationExtra Init.WFTactics
use crate::ffi::{lean_nat_dec_lt, lean_nat_mul};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
pub unsafe fn l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(
    mut v_n_23_: *mut leanh::LeanObject,
    mut v_power_24_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_25_: u8 = 0;
    let mut v___x_26_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_27_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_25_ = lean_nat_dec_lt(v_power_24_, v_n_23_);
                if v___x_25_ == 0 {
                    return v_power_24_;
                } else {
                    v___x_26_ = leanh::lean_unsigned_to_nat(2);
                    v___x_27_ = lean_nat_mul(v_power_24_, v___x_26_);
                    leanh::lean_dec(v_power_24_);
                    v_power_24_ = v___x_27_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg___boxed(
    mut v_n_29_: *mut leanh::LeanObject,
    mut v_power_30_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_31_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_31_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(
        v_n_29_,
        v_power_30_,
    );
    leanh::lean_dec(v_n_29_);
    return v_res_31_;
}
pub unsafe fn l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go(
    mut v_n_32_: *mut leanh::LeanObject,
    mut v_power_33_: *mut leanh::LeanObject,
    mut v_h_34_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_35_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_35_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(
        v_n_32_,
        v_power_33_,
    );
    return v___x_35_;
}
pub unsafe fn l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___boxed(
    mut v_n_36_: *mut leanh::LeanObject,
    mut v_power_37_: *mut leanh::LeanObject,
    mut v_h_38_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_39_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_39_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go(
        v_n_36_,
        v_power_37_,
        v_h_38_,
    );
    leanh::lean_dec(v_n_36_);
    return v_res_39_;
}
pub unsafe fn l_Nat_nextPowerOfTwo(
    mut v_n_40_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_41_ = leanh::lean_unsigned_to_nat(1);
    v___x_42_ = l___private_Init_Data_Nat_Power2_Basic_0__Nat_nextPowerOfTwo_go___redArg(
        v_n_40_, v___x_41_,
    );
    return v___x_42_;
}
pub unsafe fn l_Nat_nextPowerOfTwo___boxed(
    mut v_n_43_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_44_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_44_ = l_Nat_nextPowerOfTwo(v_n_43_);
    leanh::lean_dec(v_n_43_);
    return v_res_44_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Power2_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Power2_Basic(
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
pub unsafe fn initialize_Init_Data_Nat_Power2_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Power2_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Power2_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Power2_Basic(builtin);
}