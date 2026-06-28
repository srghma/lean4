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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_DHashMap_Equiv_instTrans(
    mut v_00_u03b1_21_: *mut LeanObject,
    mut v_00_u03b2_22_: *mut LeanObject,
    mut v_x_23_: *mut LeanObject,
    mut v_x_24_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_25_: *mut LeanObject = core::ptr::null_mut();
    v___x_25_ = lean_box(0);
    return v___x_25_;
}
pub unsafe fn l_Std_DHashMap_Equiv_instTrans___boxed(
    mut v_00_u03b1_26_: *mut LeanObject,
    mut v_00_u03b2_27_: *mut LeanObject,
    mut v_x_28_: *mut LeanObject,
    mut v_x_29_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_30_: *mut LeanObject = core::ptr::null_mut();
    v_res_30_ = l_Std_DHashMap_Equiv_instTrans(v_00_u03b1_26_, v_00_u03b2_27_, v_x_28_, v_x_29_);
    lean_dec_ref(v_x_29_);
    lean_dec_ref(v_x_28_);
    return v_res_30_;
}
pub unsafe fn l_Std_DHashMap_isSetoid(
    mut v_00_u03b1_31_: *mut LeanObject,
    mut v_00_u03b2_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
    mut v_inst_34_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
    v___x_35_ = lean_box(0);
    return v___x_35_;
}
pub unsafe fn l_Std_DHashMap_isSetoid___boxed(
    mut v_00_u03b1_36_: *mut LeanObject,
    mut v_00_u03b2_37_: *mut LeanObject,
    mut v_inst_38_: *mut LeanObject,
    mut v_inst_39_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_40_: *mut LeanObject = core::ptr::null_mut();
    v_res_40_ = l_Std_DHashMap_isSetoid(v_00_u03b1_36_, v_00_u03b2_37_, v_inst_38_, v_inst_39_);
    lean_dec_ref(v_inst_39_);
    lean_dec_ref(v_inst_38_);
    return v_res_40_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DHashMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DHashMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DHashMap_Lemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DHashMap_Internal_RawLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_AdditionalOperations(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Pairwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_DHashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_DHashMap_Lemmas(builtin);
}
