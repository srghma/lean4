// Lean compiler output
// Module: Lean.Elab.ConfigEval
// Imports: Lean.Elab.ConfigEval.Types Lean.Elab.ConfigEval.Basic Lean.Elab.ConfigEval.Commands Lean.Elab.ConfigEval.DeriveEvalTerm Lean.Elab.ConfigEval.DeriveEvalExpr Lean.Elab.ConfigEval.DeriveEvalConfigItem Lean.Elab.ConfigEval.Instances Lean.Elab.ConfigEval.MetaInstances Lean.Elab.ConfigEval.Extra
use crate::r#gen::Lean::Elab::ConfigEval::Basic::{
    initialize_Lean_Elab_ConfigEval_Basic, runtime_initialize_Lean_Elab_ConfigEval_Basic,
};
use crate::r#gen::Lean::Elab::ConfigEval::Commands::{
    initialize_Lean_Elab_ConfigEval_Commands, runtime_initialize_Lean_Elab_ConfigEval_Commands,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalConfigItem::{
    initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem,
    runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalExpr::{
    initialize_Lean_Elab_ConfigEval_DeriveEvalExpr,
    runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalTerm::{
    initialize_Lean_Elab_ConfigEval_DeriveEvalTerm,
    runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm,
};
use crate::r#gen::Lean::Elab::ConfigEval::Extra::{
    initialize_Lean_Elab_ConfigEval_Extra, runtime_initialize_Lean_Elab_ConfigEval_Extra,
};
use crate::r#gen::Lean::Elab::ConfigEval::Instances::{
    initialize_Lean_Elab_ConfigEval_Instances, runtime_initialize_Lean_Elab_ConfigEval_Instances,
};
use crate::r#gen::Lean::Elab::ConfigEval::MetaInstances::{
    initialize_Lean_Elab_ConfigEval_MetaInstances,
    runtime_initialize_Lean_Elab_ConfigEval_MetaInstances,
};
use crate::r#gen::Lean::Elab::ConfigEval::Types::{
    initialize_Lean_Elab_ConfigEval_Types, runtime_initialize_Lean_Elab_ConfigEval_Types,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval(builtin);
}
