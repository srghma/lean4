// Lean compiler output
// Module: Init.Data.String.Lemmas.Pattern.TakeDrop
// Imports: Init.Data.String.Lemmas.Pattern.TakeDrop.Basic Init.Data.String.Lemmas.Pattern.TakeDrop.Char Init.Data.String.Lemmas.Pattern.TakeDrop.Pred Init.Data.String.Lemmas.Pattern.TakeDrop.String
use crate::r#gen::Init::Data::String::Lemmas::Pattern::TakeDrop::Basic::{
    initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::TakeDrop::Char::{
    initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::TakeDrop::Pred::{
    initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred,
};
use crate::r#gen::Init::Data::String::Lemmas::Pattern::TakeDrop::String::{
    initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_String,
    runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_String,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Lemmas_Pattern_TakeDrop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Char(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Pattern_TakeDrop_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Lemmas_Pattern_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Lemmas_Pattern_TakeDrop(builtin);
}
