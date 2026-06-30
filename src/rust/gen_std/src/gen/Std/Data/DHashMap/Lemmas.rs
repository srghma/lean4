// Lean compiler output
// Module: Std.Data.DHashMap.Lemmas
// Imports: Std.Data.DHashMap.Internal.RawLemmas Std.Data.DHashMap.Basic Std.Data.DHashMap.AdditionalOperations Std.Data.DHashMap.AdditionalOperations Init.ByCases Init.Data.List.Find Init.Data.List.Impl Init.Data.List.Pairwise Init.Data.Prod
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Data::List::Pairwise::{
    initialize_Init_Data_List_Pairwise, runtime_initialize_Init_Data_List_Pairwise,
};
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Std::Data::DHashMap::AdditionalOperations::{
    initialize_Std_Data_DHashMap_AdditionalOperations,
    runtime_initialize_Std_Data_DHashMap_AdditionalOperations,
};
use crate::r#gen::Std::Data::DHashMap::Basic::{
    initialize_Std_Data_DHashMap_Basic, runtime_initialize_Std_Data_DHashMap_Basic,
};
use crate::r#gen::Std::Data::DHashMap::Internal::RawLemmas::{
    initialize_Std_Data_DHashMap_Internal_RawLemmas,
    runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas,
};
pub unsafe fn l_Std_DHashMap_Equiv_instTrans(
    mut v_00_u03b1_21_: *mut leanh::LeanObject,
    mut v_00_u03b2_22_: *mut leanh::LeanObject,
    mut v_x_23_: *mut leanh::LeanObject,
    mut v_x_24_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_25_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_25_ = leanh::lean_box(0);
    return v___x_25_;
}
pub unsafe fn l_Std_DHashMap_Equiv_instTrans___boxed(
    mut v_00_u03b1_26_: *mut leanh::LeanObject,
    mut v_00_u03b2_27_: *mut leanh::LeanObject,
    mut v_x_28_: *mut leanh::LeanObject,
    mut v_x_29_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_30_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_30_ = l_Std_DHashMap_Equiv_instTrans(v_00_u03b1_26_, v_00_u03b2_27_, v_x_28_, v_x_29_);
    leanh::lean_dec_ref(v_x_29_);
    leanh::lean_dec_ref(v_x_28_);
    return v_res_30_;
}
pub unsafe fn l_Std_DHashMap_isSetoid(
    mut v_00_u03b1_31_: *mut leanh::LeanObject,
    mut v_00_u03b2_32_: *mut leanh::LeanObject,
    mut v_inst_33_: *mut leanh::LeanObject,
    mut v_inst_34_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_35_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_35_ = leanh::lean_box(0);
    return v___x_35_;
}
pub unsafe fn l_Std_DHashMap_isSetoid___boxed(
    mut v_00_u03b1_36_: *mut leanh::LeanObject,
    mut v_00_u03b2_37_: *mut leanh::LeanObject,
    mut v_inst_38_: *mut leanh::LeanObject,
    mut v_inst_39_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_40_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_40_ = l_Std_DHashMap_isSetoid(v_00_u03b1_36_, v_00_u03b2_37_, v_inst_38_, v_inst_39_);
    leanh::lean_dec_ref(v_inst_39_);
    leanh::lean_dec_ref(v_inst_38_);
    return v_res_40_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
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
pub unsafe fn meta_initialize_Std_Data_DHashMap_Lemmas(
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
pub unsafe fn initialize_Std_Data_DHashMap_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
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
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Lemmas(builtin);
}