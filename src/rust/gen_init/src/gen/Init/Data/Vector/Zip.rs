// Lean compiler output
// Module: Init.Data.Vector.Zip
// Imports: Init.Data.Array.Basic Init.Data.Vector.Basic Init.Data.Function Init.Data.Vector.Basic Init.Data.Array.Zip Init.Data.Vector.Lemmas
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Zip::{
    initialize_Init_Data_Array_Zip, runtime_initialize_Init_Data_Array_Zip,
};
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_43_: *mut leanh::LeanObject,
    mut v_x_44_: *mut leanh::LeanObject,
    mut v_h__1_45_: *mut leanh::LeanObject,
    mut v_h__2_46_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_43_) == 1 {
        if leanh::lean_obj_tag(v_x_44_) == 1 {
            let mut v_val_47_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_48_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_49_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_46_);
            v_val_47_ = leanh::lean_ctor_get(v_x_43_, 0);
            leanh::lean_inc(v_val_47_);
            leanh::lean_dec_ref_known(v_x_43_, 1);
            v_val_48_ = leanh::lean_ctor_get(v_x_44_, 0);
            leanh::lean_inc(v_val_48_);
            leanh::lean_dec_ref_known(v_x_44_, 1);
            v___x_49_ = leanh::lean_apply_2(v_h__1_45_, v_val_47_, v_val_48_);
            return v___x_49_;
        } else {
            let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_45_);
            v___x_50_ =
                leanh::lean_apply_3(v_h__2_46_, v_x_43_, v_x_44_, leanh::lean_box(0));
            return v___x_50_;
        }
    } else {
        let mut v___x_51_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_45_);
        v___x_51_ =
            leanh::lean_apply_3(v_h__2_46_, v_x_43_, v_x_44_, leanh::lean_box(0));
        return v___x_51_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_52_: *mut leanh::LeanObject,
    mut v_00_u03b2_53_: *mut leanh::LeanObject,
    mut v_motive_54_: *mut leanh::LeanObject,
    mut v_x_55_: *mut leanh::LeanObject,
    mut v_x_56_: *mut leanh::LeanObject,
    mut v_h__1_57_: *mut leanh::LeanObject,
    mut v_h__2_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_55_) == 1 {
        if leanh::lean_obj_tag(v_x_56_) == 1 {
            let mut v_val_59_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_60_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_58_);
            v_val_59_ = leanh::lean_ctor_get(v_x_55_, 0);
            leanh::lean_inc(v_val_59_);
            leanh::lean_dec_ref_known(v_x_55_, 1);
            v_val_60_ = leanh::lean_ctor_get(v_x_56_, 0);
            leanh::lean_inc(v_val_60_);
            leanh::lean_dec_ref_known(v_x_56_, 1);
            v___x_61_ = leanh::lean_apply_2(v_h__1_57_, v_val_59_, v_val_60_);
            return v___x_61_;
        } else {
            let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_57_);
            v___x_62_ =
                leanh::lean_apply_3(v_h__2_58_, v_x_55_, v_x_56_, leanh::lean_box(0));
            return v___x_62_;
        }
    } else {
        let mut v___x_63_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_57_);
        v___x_63_ =
            leanh::lean_apply_3(v_h__2_58_, v_x_55_, v_x_56_, leanh::lean_box(0));
        return v___x_63_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Vector_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_64_: *mut leanh::LeanObject,
    mut v_x_65_: *mut leanh::LeanObject,
    mut v_h__1_66_: *mut leanh::LeanObject,
    mut v_h__2_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_64_) == 1 {
        if leanh::lean_obj_tag(v_x_65_) == 1 {
            let mut v_val_68_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_69_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_67_);
            v_val_68_ = leanh::lean_ctor_get(v_x_64_, 0);
            leanh::lean_inc(v_val_68_);
            leanh::lean_dec_ref_known(v_x_64_, 1);
            v_val_69_ = leanh::lean_ctor_get(v_x_65_, 0);
            leanh::lean_inc(v_val_69_);
            leanh::lean_dec_ref_known(v_x_65_, 1);
            v___x_70_ = leanh::lean_apply_2(v_h__1_66_, v_val_68_, v_val_69_);
            return v___x_70_;
        } else {
            let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_66_);
            v___x_71_ =
                leanh::lean_apply_3(v_h__2_67_, v_x_64_, v_x_65_, leanh::lean_box(0));
            return v___x_71_;
        }
    } else {
        let mut v___x_72_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_66_);
        v___x_72_ =
            leanh::lean_apply_3(v_h__2_67_, v_x_64_, v_x_65_, leanh::lean_box(0));
        return v___x_72_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Vector_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_73_: *mut leanh::LeanObject,
    mut v_00_u03b2_74_: *mut leanh::LeanObject,
    mut v_motive_75_: *mut leanh::LeanObject,
    mut v_x_76_: *mut leanh::LeanObject,
    mut v_x_77_: *mut leanh::LeanObject,
    mut v_h__1_78_: *mut leanh::LeanObject,
    mut v_h__2_79_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_76_) == 1 {
        if leanh::lean_obj_tag(v_x_77_) == 1 {
            let mut v_val_80_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_81_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_79_);
            v_val_80_ = leanh::lean_ctor_get(v_x_76_, 0);
            leanh::lean_inc(v_val_80_);
            leanh::lean_dec_ref_known(v_x_76_, 1);
            v_val_81_ = leanh::lean_ctor_get(v_x_77_, 0);
            leanh::lean_inc(v_val_81_);
            leanh::lean_dec_ref_known(v_x_77_, 1);
            v___x_82_ = leanh::lean_apply_2(v_h__1_78_, v_val_80_, v_val_81_);
            return v___x_82_;
        } else {
            let mut v___x_83_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_78_);
            v___x_83_ =
                leanh::lean_apply_3(v_h__2_79_, v_x_76_, v_x_77_, leanh::lean_box(0));
            return v___x_83_;
        }
    } else {
        let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_78_);
        v___x_84_ =
            leanh::lean_apply_3(v_h__2_79_, v_x_76_, v_x_77_, leanh::lean_box(0));
        return v___x_84_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Zip(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Zip(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Zip(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Zip(builtin);
}