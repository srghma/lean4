// Lean compiler output
// Module: Lean.Data.Json
// Imports: Lean.Data.Json.Stream Lean.Data.Json.Printer Lean.Data.Json.Parser Lean.Data.Json.FromToJson Lean.Data.Json.Elab
use crate::r#gen::Lean::Data::Json::Elab::{
    initialize_Lean_Data_Json_Elab, runtime_initialize_Lean_Data_Json_Elab,
};
use crate::r#gen::Lean::Data::Json::FromToJson::{
    initialize_Lean_Data_Json_FromToJson, runtime_initialize_Lean_Data_Json_FromToJson,
};
use crate::r#gen::Lean::Data::Json::Parser::{
    initialize_Lean_Data_Json_Parser, runtime_initialize_Lean_Data_Json_Parser,
};
use crate::r#gen::Lean::Data::Json::Printer::{
    initialize_Lean_Data_Json_Printer, runtime_initialize_Lean_Data_Json_Printer,
};
use crate::r#gen::Lean::Data::Json::Stream::{
    initialize_Lean_Data_Json_Stream, runtime_initialize_Lean_Data_Json_Stream,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Printer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_FromToJson(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Elab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json_Printer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json_FromToJson(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json_Elab(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Json(builtin);
}
