// Lean compiler output
// Module: Init.Data.Sum.Lemmas
// Imports: Init.Data.Sum.Basic Init.Data.Sum.Basic Init.Ext
use crate::r#gen::Init::Data::Sum::Basic::{
    initialize_Init_Data_Sum_Basic, runtime_initialize_Init_Data_Sum_Basic,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Sum_Lemmas_0__Sum_isLeft_match__1_splitter___redArg(
    mut v_x_35_: *mut LeanObject,
    mut v_h__1_36_: *mut LeanObject,
    mut v_h__2_37_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_35_) == 0 {
        let mut v_val_38_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_37_);
        v_val_38_ = lean_ctor_get(v_x_35_, 0);
        lean_inc(v_val_38_);
        lean_dec_ref_known(v_x_35_, 1);
        v___x_39_ = lean_apply_1(v_h__1_36_, v_val_38_);
        return v___x_39_;
    } else {
        let mut v_val_40_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_36_);
        v_val_40_ = lean_ctor_get(v_x_35_, 0);
        lean_inc(v_val_40_);
        lean_dec_ref_known(v_x_35_, 1);
        v___x_41_ = lean_apply_1(v_h__2_37_, v_val_40_);
        return v___x_41_;
    }
}
pub unsafe fn l___private_Init_Data_Sum_Lemmas_0__Sum_isLeft_match__1_splitter(
    mut v_00_u03b1_42_: *mut LeanObject,
    mut v_00_u03b2_43_: *mut LeanObject,
    mut v_motive_44_: *mut LeanObject,
    mut v_x_45_: *mut LeanObject,
    mut v_h__1_46_: *mut LeanObject,
    mut v_h__2_47_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_45_) == 0 {
        let mut v_val_48_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_47_);
        v_val_48_ = lean_ctor_get(v_x_45_, 0);
        lean_inc(v_val_48_);
        lean_dec_ref_known(v_x_45_, 1);
        v___x_49_ = lean_apply_1(v_h__1_46_, v_val_48_);
        return v___x_49_;
    } else {
        let mut v_val_50_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_46_);
        v_val_50_ = lean_ctor_get(v_x_45_, 0);
        lean_inc(v_val_50_);
        lean_dec_ref_known(v_x_45_, 1);
        v___x_51_ = lean_apply_1(v_h__2_47_, v_val_50_);
        return v___x_51_;
    }
}
pub unsafe fn l___private_Init_Data_Sum_Lemmas_0__Sum_getRight_x3f_match__1_splitter___redArg(
    mut v_x_52_: *mut LeanObject,
    mut v_h__1_53_: *mut LeanObject,
    mut v_h__2_54_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_52_) == 0 {
        let mut v_val_55_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_56_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_53_);
        v_val_55_ = lean_ctor_get(v_x_52_, 0);
        lean_inc(v_val_55_);
        lean_dec_ref_known(v_x_52_, 1);
        v___x_56_ = lean_apply_1(v_h__2_54_, v_val_55_);
        return v___x_56_;
    } else {
        let mut v_val_57_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_58_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_54_);
        v_val_57_ = lean_ctor_get(v_x_52_, 0);
        lean_inc(v_val_57_);
        lean_dec_ref_known(v_x_52_, 1);
        v___x_58_ = lean_apply_1(v_h__1_53_, v_val_57_);
        return v___x_58_;
    }
}
pub unsafe fn l___private_Init_Data_Sum_Lemmas_0__Sum_getRight_x3f_match__1_splitter(
    mut v_00_u03b1_59_: *mut LeanObject,
    mut v_00_u03b2_60_: *mut LeanObject,
    mut v_motive_61_: *mut LeanObject,
    mut v_x_62_: *mut LeanObject,
    mut v_h__1_63_: *mut LeanObject,
    mut v_h__2_64_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_62_) == 0 {
        let mut v_val_65_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_63_);
        v_val_65_ = lean_ctor_get(v_x_62_, 0);
        lean_inc(v_val_65_);
        lean_dec_ref_known(v_x_62_, 1);
        v___x_66_ = lean_apply_1(v_h__2_64_, v_val_65_);
        return v___x_66_;
    } else {
        let mut v_val_67_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_64_);
        v_val_67_ = lean_ctor_get(v_x_62_, 0);
        lean_inc(v_val_67_);
        lean_dec_ref_known(v_x_62_, 1);
        v___x_68_ = lean_apply_1(v_h__1_63_, v_val_67_);
        return v___x_68_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Sum_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Sum_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Sum_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Sum_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Sum_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Sum_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Sum_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Sum_Lemmas(builtin);
}
