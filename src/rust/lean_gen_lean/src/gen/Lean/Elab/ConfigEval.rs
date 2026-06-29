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
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ConfigEval(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_ConfigEval_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ConfigEval(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ConfigEval(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_ConfigEval_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Commands(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_DeriveEvalConfigItem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_MetaInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval_Extra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ConfigEval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ConfigEval(builtin);
}
