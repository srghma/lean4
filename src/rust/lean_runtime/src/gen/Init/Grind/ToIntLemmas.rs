// Lean compiler output
// Module: Init.Grind.ToIntLemmas
// Imports: Init.Grind.ToInt Init.Grind.ToInt Init.Data.Option.Basic
use crate::r#gen::Init::Data::Option::Basic::{
    initialize_Init_Data_Option_Basic, runtime_initialize_Init_Data_Option_Basic,
};
use crate::r#gen::Init::Grind::ToInt::{
    initialize_Init_Grind_ToInt, runtime_initialize_Init_Grind_ToInt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter___redArg(
    mut v_i_30_: *mut LeanObject,
    mut v_h__1_31_: *mut LeanObject,
    mut v_h__2_32_: *mut LeanObject,
    mut v_h__3_33_: *mut LeanObject,
    mut v_h__4_34_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_i_30_) {
        0 => {
            let mut v_lo_35_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_36_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_34_);
            lean_dec(v_h__3_33_);
            lean_dec(v_h__2_32_);
            v_lo_35_ = lean_ctor_get(v_i_30_, 0);
            lean_inc(v_lo_35_);
            v_hi_36_ = lean_ctor_get(v_i_30_, 1);
            lean_inc(v_hi_36_);
            lean_dec_ref_known(v_i_30_, 2);
            v___x_37_ = lean_apply_2(v_h__1_31_, v_lo_35_, v_hi_36_);
            return v___x_37_;
        }
        1 => {
            let mut v_lo_38_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_34_);
            lean_dec(v_h__3_33_);
            lean_dec(v_h__1_31_);
            v_lo_38_ = lean_ctor_get(v_i_30_, 0);
            lean_inc(v_lo_38_);
            lean_dec_ref_known(v_i_30_, 1);
            v___x_39_ = lean_apply_1(v_h__2_32_, v_lo_38_);
            return v___x_39_;
        }
        2 => {
            let mut v_hi_40_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_34_);
            lean_dec(v_h__2_32_);
            lean_dec(v_h__1_31_);
            v_hi_40_ = lean_ctor_get(v_i_30_, 0);
            lean_inc(v_hi_40_);
            lean_dec_ref_known(v_i_30_, 1);
            v___x_41_ = lean_apply_1(v_h__3_33_, v_hi_40_);
            return v___x_41_;
        }
        _ => {
            let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_43_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_33_);
            lean_dec(v_h__2_32_);
            lean_dec(v_h__1_31_);
            v___x_42_ = lean_box(0);
            v___x_43_ = lean_apply_1(v_h__4_34_, v___x_42_);
            return v___x_43_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_ToIntLemmas_0__Lean_Grind_IntInterval_lo_x3f_match__1_splitter(
    mut v_motive_44_: *mut LeanObject,
    mut v_i_45_: *mut LeanObject,
    mut v_h__1_46_: *mut LeanObject,
    mut v_h__2_47_: *mut LeanObject,
    mut v_h__3_48_: *mut LeanObject,
    mut v_h__4_49_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_i_45_) {
        0 => {
            let mut v_lo_50_: *mut LeanObject = core::ptr::null_mut();
            let mut v_hi_51_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_52_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_49_);
            lean_dec(v_h__3_48_);
            lean_dec(v_h__2_47_);
            v_lo_50_ = lean_ctor_get(v_i_45_, 0);
            lean_inc(v_lo_50_);
            v_hi_51_ = lean_ctor_get(v_i_45_, 1);
            lean_inc(v_hi_51_);
            lean_dec_ref_known(v_i_45_, 2);
            v___x_52_ = lean_apply_2(v_h__1_46_, v_lo_50_, v_hi_51_);
            return v___x_52_;
        }
        1 => {
            let mut v_lo_53_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_49_);
            lean_dec(v_h__3_48_);
            lean_dec(v_h__1_46_);
            v_lo_53_ = lean_ctor_get(v_i_45_, 0);
            lean_inc(v_lo_53_);
            lean_dec_ref_known(v_i_45_, 1);
            v___x_54_ = lean_apply_1(v_h__2_47_, v_lo_53_);
            return v___x_54_;
        }
        2 => {
            let mut v_hi_55_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_56_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_49_);
            lean_dec(v_h__2_47_);
            lean_dec(v_h__1_46_);
            v_hi_55_ = lean_ctor_get(v_i_45_, 0);
            lean_inc(v_hi_55_);
            lean_dec_ref_known(v_i_45_, 1);
            v___x_56_ = lean_apply_1(v_h__3_48_, v_hi_55_);
            return v___x_56_;
        }
        _ => {
            let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_48_);
            lean_dec(v_h__2_47_);
            lean_dec(v_h__1_46_);
            v___x_57_ = lean_box(0);
            v___x_58_ = lean_apply_1(v_h__4_49_, v___x_57_);
            return v___x_58_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_ToIntLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_ToIntLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_ToIntLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_ToInt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_ToIntLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_ToIntLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_ToIntLemmas(builtin);
}
