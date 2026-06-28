// Lean compiler output
// Module: Lake.CLI
// Imports: Lake.CLI.Actions Lake.CLI.Build Lake.CLI.Error Lake.CLI.Help Lake.CLI.Init Lake.CLI.Main Lake.CLI.Serve Lake.CLI.Shake Lake.CLI.Translate Lake.CLI.Translate.Lean Lake.CLI.Translate.Toml
use crate::r#gen::Lake::CLI::Actions::{
    initialize_Lake_CLI_Actions, runtime_initialize_Lake_CLI_Actions,
};
use crate::r#gen::Lake::CLI::Build::{
    initialize_Lake_CLI_Build, runtime_initialize_Lake_CLI_Build,
};
use crate::r#gen::Lake::CLI::Error::{
    initialize_Lake_CLI_Error, runtime_initialize_Lake_CLI_Error,
};
use crate::r#gen::Lake::CLI::Help::{initialize_Lake_CLI_Help, runtime_initialize_Lake_CLI_Help};
use crate::r#gen::Lake::CLI::Init::{initialize_Lake_CLI_Init, runtime_initialize_Lake_CLI_Init};
use crate::r#gen::Lake::CLI::Main::{initialize_Lake_CLI_Main, runtime_initialize_Lake_CLI_Main};
use crate::r#gen::Lake::CLI::Serve::{
    initialize_Lake_CLI_Serve, runtime_initialize_Lake_CLI_Serve,
};
use crate::r#gen::Lake::CLI::Shake::{
    initialize_Lake_CLI_Shake, runtime_initialize_Lake_CLI_Shake,
};
use crate::r#gen::Lake::CLI::Translate::Lean::{
    initialize_Lake_CLI_Translate_Lean, runtime_initialize_Lake_CLI_Translate_Lean,
};
use crate::r#gen::Lake::CLI::Translate::Toml::{
    initialize_Lake_CLI_Translate_Toml, runtime_initialize_Lake_CLI_Translate_Toml,
};
use crate::r#gen::Lake::CLI::Translate::{
    initialize_Lake_CLI_Translate, runtime_initialize_Lake_CLI_Translate,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_CLI(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_CLI_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Build(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Help(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Serve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Shake(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Translate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Translate_Lean(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI_Translate_Toml(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_CLI(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_CLI(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_CLI_Actions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Build(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Error(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Help(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Init(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Serve(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Shake(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Translate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Translate_Lean(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_CLI_Translate_Toml(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_CLI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_CLI(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_CLI(builtin);
}
