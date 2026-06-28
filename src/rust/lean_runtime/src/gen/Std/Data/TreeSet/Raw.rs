// Lean compiler output
// Module: Std.Data.TreeSet.Raw
// Imports: Std.Data.TreeSet.Raw.Basic Std.Data.TreeSet.Raw.Lemmas Std.Data.TreeSet.Raw.WF Std.Data.TreeSet.Raw.Iterator Std.Data.TreeSet.Raw.Slice Std.Data.TreeSet.Raw.DecidableEquiv
use crate::r#gen::Std::Data::TreeSet::Raw::Basic::{
    initialize_Std_Data_TreeSet_Raw_Basic, runtime_initialize_Std_Data_TreeSet_Raw_Basic,
};
use crate::r#gen::Std::Data::TreeSet::Raw::DecidableEquiv::{
    initialize_Std_Data_TreeSet_Raw_DecidableEquiv,
    runtime_initialize_Std_Data_TreeSet_Raw_DecidableEquiv,
};
use crate::r#gen::Std::Data::TreeSet::Raw::Iterator::{
    initialize_Std_Data_TreeSet_Raw_Iterator, runtime_initialize_Std_Data_TreeSet_Raw_Iterator,
};
use crate::r#gen::Std::Data::TreeSet::Raw::Lemmas::{
    initialize_Std_Data_TreeSet_Raw_Lemmas, runtime_initialize_Std_Data_TreeSet_Raw_Lemmas,
};
use crate::r#gen::Std::Data::TreeSet::Raw::Slice::{
    initialize_Std_Data_TreeSet_Raw_Slice, runtime_initialize_Std_Data_TreeSet_Raw_Slice,
};
use crate::r#gen::Std::Data::TreeSet::Raw::WF::{
    initialize_Std_Data_TreeSet_Raw_WF, runtime_initialize_Std_Data_TreeSet_Raw_WF,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_TreeSet_Raw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_TreeSet_Raw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_TreeSet_Raw(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_TreeSet_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Raw_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Raw_WF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Raw_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Raw_Slice(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeSet_Raw_DecidableEquiv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeSet_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_TreeSet_Raw(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_TreeSet_Raw(builtin);
}
