// Lean compiler output
// Module: Init.Grind.ToIntLemmas
// Imports: Init.Grind.ToInt Init.Grind.ToInt Init.Data.Option.Basic
use crate::r#gen::Init::Data::Option::Basic::{
    initialize_Init_Data_Option_Basic, runtime_initialize_Init_Data_Option_Basic,
};
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
pub unsafe fn l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(
    mut v_i_30_: *mut crate::leanh::LeanObject,
    mut v_h__1_31_: *mut crate::leanh::LeanObject,
    mut v_h__2_32_: *mut crate::leanh::LeanObject,
    mut v_h__3_33_: *mut crate::leanh::LeanObject,
    mut v_h__4_34_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_i_30_) {
        0 => {
            let mut v_lo_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_34_);
            crate::leanh::lean_dec(v_h__3_33_);
            crate::leanh::lean_dec(v_h__2_32_);
            v_lo_35_ = crate::leanh::lean_ctor_get(v_i_30_, 0);
            crate::leanh::lean_inc(v_lo_35_);
            v_hi_36_ = crate::leanh::lean_ctor_get(v_i_30_, 1);
            crate::leanh::lean_inc(v_hi_36_);
            crate::leanh::lean_dec_ref_known(v_i_30_, 2);
            v___x_37_ = crate::leanh::lean_apply_2(v_h__1_31_, v_lo_35_, v_hi_36_);
            return v___x_37_;
        }
        1 => {
            let mut v_lo_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_34_);
            crate::leanh::lean_dec(v_h__3_33_);
            crate::leanh::lean_dec(v_h__1_31_);
            v_lo_38_ = crate::leanh::lean_ctor_get(v_i_30_, 0);
            crate::leanh::lean_inc(v_lo_38_);
            crate::leanh::lean_dec_ref_known(v_i_30_, 1);
            v___x_39_ = crate::leanh::lean_apply_1(v_h__2_32_, v_lo_38_);
            return v___x_39_;
        }
        2 => {
            let mut v_hi_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_34_);
            crate::leanh::lean_dec(v_h__2_32_);
            crate::leanh::lean_dec(v_h__1_31_);
            v_hi_40_ = crate::leanh::lean_ctor_get(v_i_30_, 0);
            crate::leanh::lean_inc(v_hi_40_);
            crate::leanh::lean_dec_ref_known(v_i_30_, 1);
            v___x_41_ = crate::leanh::lean_apply_1(v_h__3_33_, v_hi_40_);
            return v___x_41_;
        }
        _ => {
            let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_43_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_33_);
            crate::leanh::lean_dec(v_h__2_32_);
            crate::leanh::lean_dec(v_h__1_31_);
            v___x_42_ = crate::leanh::lean_box(0);
            v___x_43_ = crate::leanh::lean_apply_1(v_h__4_34_, v___x_42_);
            return v___x_43_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(
    mut v_motive_44_: *mut crate::leanh::LeanObject,
    mut v_i_45_: *mut crate::leanh::LeanObject,
    mut v_h__1_46_: *mut crate::leanh::LeanObject,
    mut v_h__2_47_: *mut crate::leanh::LeanObject,
    mut v_h__3_48_: *mut crate::leanh::LeanObject,
    mut v_h__4_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_i_45_) {
        0 => {
            let mut v_lo_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_hi_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_49_);
            crate::leanh::lean_dec(v_h__3_48_);
            crate::leanh::lean_dec(v_h__2_47_);
            v_lo_50_ = crate::leanh::lean_ctor_get(v_i_45_, 0);
            crate::leanh::lean_inc(v_lo_50_);
            v_hi_51_ = crate::leanh::lean_ctor_get(v_i_45_, 1);
            crate::leanh::lean_inc(v_hi_51_);
            crate::leanh::lean_dec_ref_known(v_i_45_, 2);
            v___x_52_ = crate::leanh::lean_apply_2(v_h__1_46_, v_lo_50_, v_hi_51_);
            return v___x_52_;
        }
        1 => {
            let mut v_lo_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_49_);
            crate::leanh::lean_dec(v_h__3_48_);
            crate::leanh::lean_dec(v_h__1_46_);
            v_lo_53_ = crate::leanh::lean_ctor_get(v_i_45_, 0);
            crate::leanh::lean_inc(v_lo_53_);
            crate::leanh::lean_dec_ref_known(v_i_45_, 1);
            v___x_54_ = crate::leanh::lean_apply_1(v_h__2_47_, v_lo_53_);
            return v___x_54_;
        }
        2 => {
            let mut v_hi_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_49_);
            crate::leanh::lean_dec(v_h__2_47_);
            crate::leanh::lean_dec(v_h__1_46_);
            v_hi_55_ = crate::leanh::lean_ctor_get(v_i_45_, 0);
            crate::leanh::lean_inc(v_hi_55_);
            crate::leanh::lean_dec_ref_known(v_i_45_, 1);
            v___x_56_ = crate::leanh::lean_apply_1(v_h__3_48_, v_hi_55_);
            return v___x_56_;
        }
        _ => {
            let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_48_);
            crate::leanh::lean_dec(v_h__2_47_);
            crate::leanh::lean_dec(v_h__1_46_);
            v___x_57_ = crate::leanh::lean_box(0);
            v___x_58_ = crate::leanh::lean_apply_1(v_h__4_49_, v___x_57_);
            return v___x_58_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_ToIntLemmas(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_ToIntLemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_ToIntLemmas(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_ToInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToIntLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_ToIntLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_ToIntLemmas(builtin);
}
