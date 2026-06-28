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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_apply_3, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_43_: *mut LeanObject,
    mut v_x_44_: *mut LeanObject,
    mut v_h__1_45_: *mut LeanObject,
    mut v_h__2_46_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_43_) == 1 {
        if lean_obj_tag(v_x_44_) == 1 {
            let mut v_val_47_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_48_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_46_);
            v_val_47_ = lean_ctor_get(v_x_43_, 0);
            lean_inc(v_val_47_);
            lean_dec_ref_known(v_x_43_, 1);
            v_val_48_ = lean_ctor_get(v_x_44_, 0);
            lean_inc(v_val_48_);
            lean_dec_ref_known(v_x_44_, 1);
            v___x_49_ = lean_apply_2(v_h__1_45_, v_val_47_, v_val_48_);
            return v___x_49_;
        } else {
            let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_45_);
            v___x_50_ = lean_apply_3(v_h__2_46_, v_x_43_, v_x_44_, lean_box(0));
            return v___x_50_;
        }
    } else {
        let mut v___x_51_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_45_);
        v___x_51_ = lean_apply_3(v_h__2_46_, v_x_43_, v_x_44_, lean_box(0));
        return v___x_51_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Array_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_52_: *mut LeanObject,
    mut v_00_u03b2_53_: *mut LeanObject,
    mut v_motive_54_: *mut LeanObject,
    mut v_x_55_: *mut LeanObject,
    mut v_x_56_: *mut LeanObject,
    mut v_h__1_57_: *mut LeanObject,
    mut v_h__2_58_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_55_) == 1 {
        if lean_obj_tag(v_x_56_) == 1 {
            let mut v_val_59_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_60_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_58_);
            v_val_59_ = lean_ctor_get(v_x_55_, 0);
            lean_inc(v_val_59_);
            lean_dec_ref_known(v_x_55_, 1);
            v_val_60_ = lean_ctor_get(v_x_56_, 0);
            lean_inc(v_val_60_);
            lean_dec_ref_known(v_x_56_, 1);
            v___x_61_ = lean_apply_2(v_h__1_57_, v_val_59_, v_val_60_);
            return v___x_61_;
        } else {
            let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_57_);
            v___x_62_ = lean_apply_3(v_h__2_58_, v_x_55_, v_x_56_, lean_box(0));
            return v___x_62_;
        }
    } else {
        let mut v___x_63_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_57_);
        v___x_63_ = lean_apply_3(v_h__2_58_, v_x_55_, v_x_56_, lean_box(0));
        return v___x_63_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Vector_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_64_: *mut LeanObject,
    mut v_x_65_: *mut LeanObject,
    mut v_h__1_66_: *mut LeanObject,
    mut v_h__2_67_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_64_) == 1 {
        if lean_obj_tag(v_x_65_) == 1 {
            let mut v_val_68_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_69_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_67_);
            v_val_68_ = lean_ctor_get(v_x_64_, 0);
            lean_inc(v_val_68_);
            lean_dec_ref_known(v_x_64_, 1);
            v_val_69_ = lean_ctor_get(v_x_65_, 0);
            lean_inc(v_val_69_);
            lean_dec_ref_known(v_x_65_, 1);
            v___x_70_ = lean_apply_2(v_h__1_66_, v_val_68_, v_val_69_);
            return v___x_70_;
        } else {
            let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_66_);
            v___x_71_ = lean_apply_3(v_h__2_67_, v_x_64_, v_x_65_, lean_box(0));
            return v___x_71_;
        }
    } else {
        let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_66_);
        v___x_72_ = lean_apply_3(v_h__2_67_, v_x_64_, v_x_65_, lean_box(0));
        return v___x_72_;
    }
}
pub unsafe fn l___private_Init_Data_Vector_Zip_0__Vector_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_73_: *mut LeanObject,
    mut v_00_u03b2_74_: *mut LeanObject,
    mut v_motive_75_: *mut LeanObject,
    mut v_x_76_: *mut LeanObject,
    mut v_x_77_: *mut LeanObject,
    mut v_h__1_78_: *mut LeanObject,
    mut v_h__2_79_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_76_) == 1 {
        if lean_obj_tag(v_x_77_) == 1 {
            let mut v_val_80_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_81_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_79_);
            v_val_80_ = lean_ctor_get(v_x_76_, 0);
            lean_inc(v_val_80_);
            lean_dec_ref_known(v_x_76_, 1);
            v_val_81_ = lean_ctor_get(v_x_77_, 0);
            lean_inc(v_val_81_);
            lean_dec_ref_known(v_x_77_, 1);
            v___x_82_ = lean_apply_2(v_h__1_78_, v_val_80_, v_val_81_);
            return v___x_82_;
        } else {
            let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_78_);
            v___x_83_ = lean_apply_3(v_h__2_79_, v_x_76_, v_x_77_, lean_box(0));
            return v___x_83_;
        }
    } else {
        let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_78_);
        v___x_84_ = lean_apply_3(v_h__2_79_, v_x_76_, v_x_77_, lean_box(0));
        return v___x_84_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Vector_Zip(builtin);
}
