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
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_54_: *mut leanh::LeanObject,
    mut v_x_55_: *mut leanh::LeanObject,
    mut v_h__1_56_: *mut leanh::LeanObject,
    mut v_h__2_57_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_54_) == 1 {
        if leanh::lean_obj_tag(v_x_55_) == 1 {
            let mut v_val_58_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_59_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_60_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_57_);
            v_val_58_ = leanh::lean_ctor_get(v_x_54_, 0);
            leanh::lean_inc(v_val_58_);
            leanh::lean_dec_ref_known(v_x_54_, 1);
            v_val_59_ = leanh::lean_ctor_get(v_x_55_, 0);
            leanh::lean_inc(v_val_59_);
            leanh::lean_dec_ref_known(v_x_55_, 1);
            v___x_60_ = leanh::lean_apply_2(v_h__1_56_, v_val_58_, v_val_59_);
            return v___x_60_;
        } else {
            let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_56_);
            v___x_61_ =
                leanh::lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, leanh::lean_box(0));
            return v___x_61_;
        }
    } else {
        let mut v___x_62_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_56_);
        v___x_62_ =
            leanh::lean_apply_3(v_h__2_57_, v_x_54_, v_x_55_, leanh::lean_box(0));
        return v___x_62_;
    }
}
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_63_: *mut leanh::LeanObject,
    mut v_00_u03b2_64_: *mut leanh::LeanObject,
    mut v_motive_65_: *mut leanh::LeanObject,
    mut v_x_66_: *mut leanh::LeanObject,
    mut v_x_67_: *mut leanh::LeanObject,
    mut v_h__1_68_: *mut leanh::LeanObject,
    mut v_h__2_69_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_66_) == 1 {
        if leanh::lean_obj_tag(v_x_67_) == 1 {
            let mut v_val_70_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_71_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_72_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_69_);
            v_val_70_ = leanh::lean_ctor_get(v_x_66_, 0);
            leanh::lean_inc(v_val_70_);
            leanh::lean_dec_ref_known(v_x_66_, 1);
            v_val_71_ = leanh::lean_ctor_get(v_x_67_, 0);
            leanh::lean_inc(v_val_71_);
            leanh::lean_dec_ref_known(v_x_67_, 1);
            v___x_72_ = leanh::lean_apply_2(v_h__1_68_, v_val_70_, v_val_71_);
            return v___x_72_;
        } else {
            let mut v___x_73_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_68_);
            v___x_73_ =
                leanh::lean_apply_3(v_h__2_69_, v_x_66_, v_x_67_, leanh::lean_box(0));
            return v___x_73_;
        }
    } else {
        let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_68_);
        v___x_74_ =
            leanh::lean_apply_3(v_h__2_69_, v_x_66_, v_x_67_, leanh::lean_box(0));
        return v___x_74_;
    }
}
pub unsafe fn l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter___redArg(
    mut v_x_75_: *mut leanh::LeanObject,
    mut v_h__1_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_77_ = leanh::lean_ctor_get(v_x_75_, 0);
    leanh::lean_inc(v_fst_77_);
    v_snd_78_ = leanh::lean_ctor_get(v_x_75_, 1);
    leanh::lean_inc(v_snd_78_);
    leanh::lean_dec_ref(v_x_75_);
    v___x_79_ = leanh::lean_apply_2(v_h__1_76_, v_fst_77_, v_snd_78_);
    return v___x_79_;
}
pub unsafe fn l___private_Init_Data_List_Zip_0__instDecidableEqProd_match__3_splitter(
    mut v_00_u03b1_80_: *mut leanh::LeanObject,
    mut v_00_u03b2_81_: *mut leanh::LeanObject,
    mut v_motive_82_: *mut leanh::LeanObject,
    mut v_x_83_: *mut leanh::LeanObject,
    mut v_h__1_84_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_85_ = leanh::lean_ctor_get(v_x_83_, 0);
    leanh::lean_inc(v_fst_85_);
    v_snd_86_ = leanh::lean_ctor_get(v_x_83_, 1);
    leanh::lean_inc(v_snd_86_);
    leanh::lean_dec_ref(v_x_83_);
    v___x_87_ = leanh::lean_apply_2(v_h__1_84_, v_fst_85_, v_snd_86_);
    return v___x_87_;
}
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_88_: *mut leanh::LeanObject,
    mut v_x_89_: *mut leanh::LeanObject,
    mut v_h__1_90_: *mut leanh::LeanObject,
    mut v_h__2_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_88_) == 0 {
        if leanh::lean_obj_tag(v_x_89_) == 0 {
            let mut v___x_92_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_91_);
            v___x_92_ = leanh::lean_box(0);
            v___x_93_ = leanh::lean_apply_1(v_h__1_90_, v___x_92_);
            return v___x_93_;
        } else {
            let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_90_);
            v___x_94_ =
                leanh::lean_apply_3(v_h__2_91_, v_x_88_, v_x_89_, leanh::lean_box(0));
            return v___x_94_;
        }
    } else {
        let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_90_);
        v___x_95_ =
            leanh::lean_apply_3(v_h__2_91_, v_x_88_, v_x_89_, leanh::lean_box(0));
        return v___x_95_;
    }
}
pub unsafe fn l___private_Init_Data_List_Zip_0__List_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_96_: *mut leanh::LeanObject,
    mut v_00_u03b2_97_: *mut leanh::LeanObject,
    mut v_motive_98_: *mut leanh::LeanObject,
    mut v_x_99_: *mut leanh::LeanObject,
    mut v_x_100_: *mut leanh::LeanObject,
    mut v_h__1_101_: *mut leanh::LeanObject,
    mut v_h__2_102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_99_) == 0 {
        if leanh::lean_obj_tag(v_x_100_) == 0 {
            let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_102_);
            v___x_103_ = leanh::lean_box(0);
            v___x_104_ = leanh::lean_apply_1(v_h__1_101_, v___x_103_);
            return v___x_104_;
        } else {
            let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_101_);
            v___x_105_ = leanh::lean_apply_3(
                v_h__2_102_,
                v_x_99_,
                v_x_100_,
                leanh::lean_box(0),
            );
            return v___x_105_;
        }
    } else {
        let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_101_);
        v___x_106_ =
            leanh::lean_apply_3(v_h__2_102_, v_x_99_, v_x_100_, leanh::lean_box(0));
        return v___x_106_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Zip(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Zip(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Zip(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Zip(builtin);
}