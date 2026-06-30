// Lean compiler output
// Module: Std.Sat.AIG.LawfulOperator
// Imports: Std.Sat.AIG.Basic Init.Omega
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Basic::{
    initialize_Std_Sat_AIG_Basic, runtime_initialize_Std_Sat_AIG_Basic,
};
pub unsafe fn l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(
    mut v_x_23_: *mut leanh::LeanObject,
    mut v_h__1_24_: *mut leanh::LeanObject,
    mut v_h__2_25_: *mut leanh::LeanObject,
    mut v_h__3_26_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_23_) {
        0 => {
            let mut v___x_27_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_26_);
            leanh::lean_dec(v_h__2_25_);
            v___x_27_ = leanh::lean_apply_1(v_h__1_24_, leanh::lean_box(0));
            return v___x_27_;
        }
        1 => {
            let mut v_idx_28_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_29_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_26_);
            leanh::lean_dec(v_h__1_24_);
            v_idx_28_ = leanh::lean_ctor_get(v_x_23_, 0);
            leanh::lean_inc(v_idx_28_);
            leanh::lean_dec_ref_known(v_x_23_, 1);
            v___x_29_ =
                leanh::lean_apply_2(v_h__2_25_, v_idx_28_, leanh::lean_box(0));
            return v___x_29_;
        }
        _ => {
            let mut v_l_30_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_31_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_25_);
            leanh::lean_dec(v_h__1_24_);
            v_l_30_ = leanh::lean_ctor_get(v_x_23_, 0);
            leanh::lean_inc(v_l_30_);
            v_r_31_ = leanh::lean_ctor_get(v_x_23_, 1);
            leanh::lean_inc(v_r_31_);
            leanh::lean_dec_ref_known(v_x_23_, 2);
            v___x_32_ =
                leanh::lean_apply_3(v_h__3_26_, v_l_30_, v_r_31_, leanh::lean_box(0));
            return v___x_32_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(
    mut v_00_u03b1_33_: *mut leanh::LeanObject,
    mut v_motive_34_: *mut leanh::LeanObject,
    mut v_x_35_: *mut leanh::LeanObject,
    mut v_h__1_36_: *mut leanh::LeanObject,
    mut v_h__2_37_: *mut leanh::LeanObject,
    mut v_h__3_38_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_35_) {
        0 => {
            let mut v___x_39_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_38_);
            leanh::lean_dec(v_h__2_37_);
            v___x_39_ = leanh::lean_apply_1(v_h__1_36_, leanh::lean_box(0));
            return v___x_39_;
        }
        1 => {
            let mut v_idx_40_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_38_);
            leanh::lean_dec(v_h__1_36_);
            v_idx_40_ = leanh::lean_ctor_get(v_x_35_, 0);
            leanh::lean_inc(v_idx_40_);
            leanh::lean_dec_ref_known(v_x_35_, 1);
            v___x_41_ =
                leanh::lean_apply_2(v_h__2_37_, v_idx_40_, leanh::lean_box(0));
            return v___x_41_;
        }
        _ => {
            let mut v_l_42_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_43_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_44_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_37_);
            leanh::lean_dec(v_h__1_36_);
            v_l_42_ = leanh::lean_ctor_get(v_x_35_, 0);
            leanh::lean_inc(v_l_42_);
            v_r_43_ = leanh::lean_ctor_get(v_x_35_, 1);
            leanh::lean_inc(v_r_43_);
            leanh::lean_dec_ref_known(v_x_35_, 2);
            v___x_44_ =
                leanh::lean_apply_3(v_h__3_38_, v_l_42_, v_r_43_, leanh::lean_box(0));
            return v___x_44_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_LawfulOperator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Sat_AIG_LawfulOperator(
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
pub unsafe fn initialize_Std_Sat_AIG_LawfulOperator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_LawfulOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_LawfulOperator(builtin);
}