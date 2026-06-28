// Lean compiler output
// Module: Std.Data.HashMap.IteratorLemmas
// Imports: Init.Data.Iterators.Lemmas.Combinators Std.Data.DHashMap.IteratorLemmas Std.Data.HashMap.Iterator Std.Data.HashMap.Iterator Std.Data.HashMap.RawLemmas Std.Data.HashMap.Lemmas Std.Data.DHashMap.Basic
use crate::r#gen::Init::Data::Iterators::Lemmas::Combinators::{
    initialize_Init_Data_Iterators_Lemmas_Combinators,
    runtime_initialize_Init_Data_Iterators_Lemmas_Combinators,
};
use crate::r#gen::Std::Data::DHashMap::Basic::{
    initialize_Std_Data_DHashMap_Basic, runtime_initialize_Std_Data_DHashMap_Basic,
};
use crate::r#gen::Std::Data::DHashMap::IteratorLemmas::{
    initialize_Std_Data_DHashMap_IteratorLemmas,
    runtime_initialize_Std_Data_DHashMap_IteratorLemmas,
};
use crate::r#gen::Std::Data::HashMap::Iterator::{
    initialize_Std_Data_HashMap_Iterator, runtime_initialize_Std_Data_HashMap_Iterator,
};
use crate::r#gen::Std::Data::HashMap::Lemmas::{
    initialize_Std_Data_HashMap_Lemmas, runtime_initialize_Std_Data_HashMap_Lemmas,
};
use crate::r#gen::Std::Data::HashMap::RawLemmas::{
    initialize_Std_Data_HashMap_RawLemmas, runtime_initialize_Std_Data_HashMap_RawLemmas,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashMap_IteratorLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_IteratorLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_RawLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashMap_IteratorLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Data_HashMap_IteratorLemmas(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Lemmas_Combinators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_IteratorLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_RawLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_HashMap_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_DHashMap_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashMap_IteratorLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashMap_IteratorLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Data_HashMap_IteratorLemmas(builtin);
}
