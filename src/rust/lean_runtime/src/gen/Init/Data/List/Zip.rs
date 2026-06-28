// Lean compiler output
// Module: Init.Data.List.Zip
// Imports: Init.Data.Function Init.Ext Init.NotationExtra Init.Data.List.Lemmas Init.Data.List.TakeDrop Init.Data.Option.Lemmas
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_apply_3, lean_box,
    lean_ctor_get, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_54_: *mut LeanObject,
    mut v_x_55_: *mut LeanObject,
    mut v_h__1_56_: *mut LeanObject,
    mut v_h__2_57_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_54_) == 1 {
        if lean_obj_tag(v_x_55_) == 1 {
            let mut v_val_58_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_59_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_60_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_57_);
            v_val_58_ = lean_ctor_get(v_x_54_, 0);
            lean_inc(v_val_58_);
            lean_dec_ref_known(v_x_54_, 1);
            v_val_59_ = lean_ctor_get(v_x_55_, 0);
            lean_inc(v_val_59_);
            lean_dec_ref_known(v_x_55_, 1);
            v___x_60_ = lean_apply_2(v_h__1_56_, v_val_58_, v_val_59_);
            return v___x_60_;
        } else {
            let mut v___x_61_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_56_);
            v___x_61_ = lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, lean_box(0));
            return v___x_61_;
        }
    } else {
        let mut v___x_62_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_56_);
        v___x_62_ = lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, lean_box(0));
        return v___x_62_;
    }
}
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_63_: *mut LeanObject,
    mut v_00_u03b2_64_: *mut LeanObject,
    mut v_motive_65_: *mut LeanObject,
    mut v_x_66_: *mut LeanObject,
    mut v_x_67_: *mut LeanObject,
    mut v_h__1_68_: *mut LeanObject,
    mut v_h__2_69_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_66_) == 1 {
        if lean_obj_tag(v_x_67_) == 1 {
            let mut v_val_70_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_71_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_72_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_69_);
            v_val_70_ = lean_ctor_get(v_x_66_, 0);
            lean_inc(v_val_70_);
            lean_dec_ref_known(v_x_66_, 1);
            v_val_71_ = lean_ctor_get(v_x_67_, 0);
            lean_inc(v_val_71_);
            lean_dec_ref_known(v_x_67_, 1);
            v___x_72_ = lean_apply_2(v_h__1_68_, v_val_70_, v_val_71_);
            return v___x_72_;
        } else {
            let mut v___x_73_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_68_);
            v___x_73_ = lean_apply_3(v_h__2_69_, v_x_66_, v_x_67_, lean_box(0));
            return v___x_73_;
        }
    } else {
        let mut v___x_74_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_68_);
        v___x_74_ = lean_apply_3(v_h__2_69_, v_x_66_, v_x_67_, lean_box(0));
        return v___x_74_;
    }
}
pub unsafe fn l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter___redArg(
    mut v_x_75_: *mut LeanObject,
    mut v_h__1_76_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_78_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    v_fst_77_ = lean_ctor_get(v_x_75_, 0);
    lean_inc(v_fst_77_);
    v_snd_78_ = lean_ctor_get(v_x_75_, 1);
    lean_inc(v_snd_78_);
    lean_dec_ref(v_x_75_);
    v___x_79_ = lean_apply_2(v_h__1_76_, v_fst_77_, v_snd_78_);
    return v___x_79_;
}
pub unsafe fn l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter(
    mut v_00_u03b1_80_: *mut LeanObject,
    mut v_00_u03b2_81_: *mut LeanObject,
    mut v_motive_82_: *mut LeanObject,
    mut v_x_83_: *mut LeanObject,
    mut v_h__1_84_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_85_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
    v_fst_85_ = lean_ctor_get(v_x_83_, 0);
    lean_inc(v_fst_85_);
    v_snd_86_ = lean_ctor_get(v_x_83_, 1);
    lean_inc(v_snd_86_);
    lean_dec_ref(v_x_83_);
    v___x_87_ = lean_apply_2(v_h__1_84_, v_fst_85_, v_snd_86_);
    return v___x_87_;
}
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_88_: *mut LeanObject,
    mut v_x_89_: *mut LeanObject,
    mut v_h__1_90_: *mut LeanObject,
    mut v_h__2_91_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_88_) == 0 {
        if lean_obj_tag(v_x_89_) == 0 {
            let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_91_);
            v___x_92_ = lean_box(0);
            v___x_93_ = lean_apply_1(v_h__1_90_, v___x_92_);
            return v___x_93_;
        } else {
            let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_90_);
            v___x_94_ = lean_apply_3(v_h__2_91_, v_x_88_, v_x_89_, lean_box(0));
            return v___x_94_;
        }
    } else {
        let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_90_);
        v___x_95_ = lean_apply_3(v_h__2_91_, v_x_88_, v_x_89_, lean_box(0));
        return v___x_95_;
    }
}
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_96_: *mut LeanObject,
    mut v_00_u03b2_97_: *mut LeanObject,
    mut v_motive_98_: *mut LeanObject,
    mut v_x_99_: *mut LeanObject,
    mut v_x_100_: *mut LeanObject,
    mut v_h__1_101_: *mut LeanObject,
    mut v_h__2_102_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_99_) == 0 {
        if lean_obj_tag(v_x_100_) == 0 {
            let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_102_);
            v___x_103_ = lean_box(0);
            v___x_104_ = lean_apply_1(v_h__1_101_, v___x_103_);
            return v___x_104_;
        } else {
            let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_101_);
            v___x_105_ = lean_apply_3(v_h__2_102_, v_x_99_, v_x_100_, lean_box(0));
            return v___x_105_;
        }
    } else {
        let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_101_);
        v___x_106_ = lean_apply_3(v_h__2_102_, v_x_99_, v_x_100_, lean_box(0));
        return v___x_106_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Zip(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_Zip(builtin);
}
