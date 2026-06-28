// Lean compiler output
// Module: Std.Sat.AIG.LawfulOperator
// Imports: Std.Sat.AIG.Basic Init.Omega
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::Basic::{
    initialize_Std_Sat_AIG_Basic, runtime_initialize_Std_Sat_AIG_Basic,
};
pub unsafe fn l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter___redArg(
    mut v_x_23_: *mut crate::leanh::LeanObject,
    mut v_h__1_24_: *mut crate::leanh::LeanObject,
    mut v_h__2_25_: *mut crate::leanh::LeanObject,
    mut v_h__3_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_23_) {
        0 => {
            let mut v___x_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_26_);
            crate::leanh::lean_dec(v_h__2_25_);
            v___x_27_ = crate::leanh::lean_apply_1(v_h__1_24_, crate::leanh::lean_box(0));
            return v___x_27_;
        }
        1 => {
            let mut v_idx_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_26_);
            crate::leanh::lean_dec(v_h__1_24_);
            v_idx_28_ = crate::leanh::lean_ctor_get(v_x_23_, 0);
            crate::leanh::lean_inc(v_idx_28_);
            crate::leanh::lean_dec_ref_known(v_x_23_, 1);
            v___x_29_ =
                crate::leanh::lean_apply_2(v_h__2_25_, v_idx_28_, crate::leanh::lean_box(0));
            return v___x_29_;
        }
        _ => {
            let mut v_l_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_31_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_25_);
            crate::leanh::lean_dec(v_h__1_24_);
            v_l_30_ = crate::leanh::lean_ctor_get(v_x_23_, 0);
            crate::leanh::lean_inc(v_l_30_);
            v_r_31_ = crate::leanh::lean_ctor_get(v_x_23_, 1);
            crate::leanh::lean_inc(v_r_31_);
            crate::leanh::lean_dec_ref_known(v_x_23_, 2);
            v___x_32_ =
                crate::leanh::lean_apply_3(v_h__3_26_, v_l_30_, v_r_31_, crate::leanh::lean_box(0));
            return v___x_32_;
        }
    }
}
pub unsafe fn l___private_Std_Sat_AIG_LawfulOperator_0__Std_Sat_AIG_toGraphviz_go_match__1_splitter(
    mut v_00_u03b1_33_: *mut crate::leanh::LeanObject,
    mut v_motive_34_: *mut crate::leanh::LeanObject,
    mut v_x_35_: *mut crate::leanh::LeanObject,
    mut v_h__1_36_: *mut crate::leanh::LeanObject,
    mut v_h__2_37_: *mut crate::leanh::LeanObject,
    mut v_h__3_38_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_35_) {
        0 => {
            let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_38_);
            crate::leanh::lean_dec(v_h__2_37_);
            v___x_39_ = crate::leanh::lean_apply_1(v_h__1_36_, crate::leanh::lean_box(0));
            return v___x_39_;
        }
        1 => {
            let mut v_idx_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_38_);
            crate::leanh::lean_dec(v_h__1_36_);
            v_idx_40_ = crate::leanh::lean_ctor_get(v_x_35_, 0);
            crate::leanh::lean_inc(v_idx_40_);
            crate::leanh::lean_dec_ref_known(v_x_35_, 1);
            v___x_41_ =
                crate::leanh::lean_apply_2(v_h__2_37_, v_idx_40_, crate::leanh::lean_box(0));
            return v___x_41_;
        }
        _ => {
            let mut v_l_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_r_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_44_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_37_);
            crate::leanh::lean_dec(v_h__1_36_);
            v_l_42_ = crate::leanh::lean_ctor_get(v_x_35_, 0);
            crate::leanh::lean_inc(v_l_42_);
            v_r_43_ = crate::leanh::lean_ctor_get(v_x_35_, 1);
            crate::leanh::lean_inc(v_r_43_);
            crate::leanh::lean_dec_ref_known(v_x_35_, 2);
            v___x_44_ =
                crate::leanh::lean_apply_3(v_h__3_38_, v_l_42_, v_r_43_, crate::leanh::lean_box(0));
            return v___x_44_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_LawfulOperator(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_Basic(builtin);
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
pub unsafe fn meta_initialize_Std_Sat_AIG_LawfulOperator(
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
pub unsafe fn initialize_Std_Sat_AIG_LawfulOperator(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_LawfulOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Sat_AIG_LawfulOperator(builtin);
}
