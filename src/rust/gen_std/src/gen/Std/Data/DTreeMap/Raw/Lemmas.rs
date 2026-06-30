// Lean compiler output
// Module: Std.Data.DTreeMap.Raw.Lemmas
// Imports: Std.Data.DTreeMap.Internal.Lemmas Std.Data.DTreeMap.Raw.AdditionalOperations Init.Data.Array.Perm Init.Data.List.Find Init.Data.List.Pairwise Init.Data.Prod
use crate::r#gen::Init::Data::Array::Perm::{
    initialize_Init_Data_Array_Perm, runtime_initialize_Init_Data_Array_Perm,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Lemmas::{
    initialize_Std_Data_DTreeMap_Internal_Lemmas,
    runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::AdditionalOperations::{
    initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
    runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
};
pub unsafe fn l_Std_DTreeMap_Raw_instCoeTypeForall__1(
    mut v_00_u03b1_27_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_28_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_28_ = leanh::lean_box(0);
    return v___x_28_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Equiv_instTrans(
    mut v_00_u03b1_29_: *mut leanh::LeanObject,
    mut v_00_u03b2_30_: *mut leanh::LeanObject,
    mut v_cmp_31_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_32_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_32_ = leanh::lean_box(0);
    return v___x_32_;
}
pub unsafe fn l_Std_DTreeMap_Raw_Equiv_instTrans___boxed(
    mut v_00_u03b1_33_: *mut leanh::LeanObject,
    mut v_00_u03b2_34_: *mut leanh::LeanObject,
    mut v_cmp_35_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_36_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_36_ = l_Std_DTreeMap_Raw_Equiv_instTrans(v_00_u03b1_33_, v_00_u03b2_34_, v_cmp_35_);
    leanh::lean_dec_ref(v_cmp_35_);
    return v_res_36_;
}
pub unsafe fn l___private_Std_Data_DTreeMap_Raw_Lemmas_0__Break_runK_match__1_splitter___redArg(
    mut v_x_37_: *mut leanh::LeanObject,
    mut v_h__1_38_: *mut leanh::LeanObject,
    mut v_h__2_39_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_37_) == 0 {
        let mut v___x_40_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_41_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_38_);
        v___x_40_ = leanh::lean_box(0);
        v___x_41_ = leanh::lean_apply_1(v_h__2_39_, v___x_40_);
        return v___x_41_;
    } else {
        let mut v_val_42_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_43_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_39_);
        v_val_42_ = leanh::lean_ctor_get(v_x_37_, 0);
        leanh::lean_inc(v_val_42_);
        leanh::lean_dec_ref_known(v_x_37_, 1);
        v___x_43_ = leanh::lean_apply_1(v_h__1_38_, v_val_42_);
        return v___x_43_;
    }
}
pub unsafe fn l___private_Std_Data_DTreeMap_Raw_Lemmas_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_44_: *mut leanh::LeanObject,
    mut v_motive_45_: *mut leanh::LeanObject,
    mut v_x_46_: *mut leanh::LeanObject,
    mut v_h__1_47_: *mut leanh::LeanObject,
    mut v_h__2_48_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_46_) == 0 {
        let mut v___x_49_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_47_);
        v___x_49_ = leanh::lean_box(0);
        v___x_50_ = leanh::lean_apply_1(v_h__2_48_, v___x_49_);
        return v___x_50_;
    } else {
        let mut v_val_51_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_48_);
        v_val_51_ = leanh::lean_ctor_get(v_x_46_, 0);
        leanh::lean_inc(v_val_51_);
        leanh::lean_dec_ref_known(v_x_46_, 1);
        v___x_52_ = leanh::lean_apply_1(v_h__1_47_, v_val_51_);
        return v___x_52_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Raw_Lemmas(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Raw_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Perm(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
}