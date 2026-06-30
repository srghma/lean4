// Lean compiler output
// Module: Std.Data.DTreeMap.Raw
// Imports: Std.Data.DTreeMap.Raw.Basic Std.Data.DTreeMap.Raw.AdditionalOperations Std.Data.DTreeMap.Raw.Lemmas Std.Data.DTreeMap.Raw.WF Std.Data.DTreeMap.Raw.Iterator Std.Data.DTreeMap.Raw.Slice Std.Data.DTreeMap.Raw.DecidableEquiv
use crate::r#gen::Std::Data::DTreeMap::Raw::AdditionalOperations::{
    initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
    runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::Basic::{
    initialize_Std_Data_DTreeMap_Raw_Basic, runtime_initialize_Std_Data_DTreeMap_Raw_Basic,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::DecidableEquiv::{
    initialize_Std_Data_DTreeMap_Raw_DecidableEquiv,
    runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::Iterator::{
    initialize_Std_Data_DTreeMap_Raw_Iterator, runtime_initialize_Std_Data_DTreeMap_Raw_Iterator,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::Lemmas::{
    initialize_Std_Data_DTreeMap_Raw_Lemmas, runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::Slice::{
    initialize_Std_Data_DTreeMap_Raw_Slice, runtime_initialize_Std_Data_DTreeMap_Raw_Slice,
};
use crate::r#gen::Std::Data::DTreeMap::Raw::WF::{
    initialize_Std_Data_DTreeMap_Raw_WF, runtime_initialize_Std_Data_DTreeMap_Raw_WF,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Raw(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_WF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_DTreeMap_Raw(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_DTreeMap_Raw_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_AdditionalOperations(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_WF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_Slice(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_DTreeMap_Raw_DecidableEquiv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Raw(builtin);
}