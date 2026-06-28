// Lean compiler output
// Module: Init.Data.List.Count
// Imports: Init.Grind.Util Init.BinderPredicates Init.Ext Init.NotationExtra Init.ByCases Init.Data.Bool Init.Data.List.Lemmas Init.Data.List.Sublist Init.Data.Option.Lemmas Init.TacticsExtra
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Grind::Util::{
    initialize_Init_Grind_Util, runtime_initialize_Init_Grind_Util,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
pub unsafe fn l___private_Init_Data_List_Count_0__List_findIdx_go_match__1_splitter___redArg(
    mut v_x_35_: *mut crate::leanh::LeanObject,
    mut v_x_36_: *mut crate::leanh::LeanObject,
    mut v_h__1_37_: *mut crate::leanh::LeanObject,
    mut v_h__2_38_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_35_) == 0 {
        let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_38_);
        v___x_39_ = crate::leanh::lean_apply_1(v_h__1_37_, v_x_36_);
        return v___x_39_;
    } else {
        let mut v_head_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_41_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_37_);
        v_head_40_ = crate::leanh::lean_ctor_get(v_x_35_, 0);
        crate::leanh::lean_inc(v_head_40_);
        v_tail_41_ = crate::leanh::lean_ctor_get(v_x_35_, 1);
        crate::leanh::lean_inc(v_tail_41_);
        crate::leanh::lean_dec_ref_known(v_x_35_, 2);
        v___x_42_ = crate::leanh::lean_apply_3(v_h__2_38_, v_head_40_, v_tail_41_, v_x_36_);
        return v___x_42_;
    }
}
pub unsafe fn l___private_Init_Data_List_Count_0__List_findIdx_go_match__1_splitter(
    mut v_00_u03b1_43_: *mut crate::leanh::LeanObject,
    mut v_motive_44_: *mut crate::leanh::LeanObject,
    mut v_x_45_: *mut crate::leanh::LeanObject,
    mut v_x_46_: *mut crate::leanh::LeanObject,
    mut v_h__1_47_: *mut crate::leanh::LeanObject,
    mut v_h__2_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_45_) == 0 {
        let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_48_);
        v___x_49_ = crate::leanh::lean_apply_1(v_h__1_47_, v_x_46_);
        return v___x_49_;
    } else {
        let mut v_head_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_47_);
        v_head_50_ = crate::leanh::lean_ctor_get(v_x_45_, 0);
        crate::leanh::lean_inc(v_head_50_);
        v_tail_51_ = crate::leanh::lean_ctor_get(v_x_45_, 1);
        crate::leanh::lean_inc(v_tail_51_);
        crate::leanh::lean_dec_ref_known(v_x_45_, 2);
        v___x_52_ = crate::leanh::lean_apply_3(v_h__2_48_, v_head_50_, v_tail_51_, v_x_46_);
        return v___x_52_;
    }
}
pub unsafe fn l___private_Init_Data_List_Count_0__List_filterMap_match__1_splitter___redArg(
    mut v_x_53_: *mut crate::leanh::LeanObject,
    mut v_h__1_54_: *mut crate::leanh::LeanObject,
    mut v_h__2_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_53_) == 0 {
        let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_55_);
        v___x_56_ = crate::leanh::lean_box(0);
        v___x_57_ = crate::leanh::lean_apply_1(v_h__1_54_, v___x_56_);
        return v___x_57_;
    } else {
        let mut v_val_58_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_54_);
        v_val_58_ = crate::leanh::lean_ctor_get(v_x_53_, 0);
        crate::leanh::lean_inc(v_val_58_);
        crate::leanh::lean_dec_ref_known(v_x_53_, 1);
        v___x_59_ = crate::leanh::lean_apply_1(v_h__2_55_, v_val_58_);
        return v___x_59_;
    }
}
pub unsafe fn l___private_Init_Data_List_Count_0__List_filterMap_match__1_splitter(
    mut v_00_u03b2_60_: *mut crate::leanh::LeanObject,
    mut v_motive_61_: *mut crate::leanh::LeanObject,
    mut v_x_62_: *mut crate::leanh::LeanObject,
    mut v_h__1_63_: *mut crate::leanh::LeanObject,
    mut v_h__2_64_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_62_) == 0 {
        let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_64_);
        v___x_65_ = crate::leanh::lean_box(0);
        v___x_66_ = crate::leanh::lean_apply_1(v_h__1_63_, v___x_65_);
        return v___x_66_;
    } else {
        let mut v_val_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_63_);
        v_val_67_ = crate::leanh::lean_ctor_get(v_x_62_, 0);
        crate::leanh::lean_inc(v_val_67_);
        crate::leanh::lean_dec_ref_known(v_x_62_, 1);
        v___x_68_ = crate::leanh::lean_apply_1(v_h__2_64_, v_val_67_);
        return v___x_68_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_Count(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_Count(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_Count(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_Count(builtin);
}
