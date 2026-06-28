// Lean compiler output
// Module: Lean.Elab.Tactic.Grind
// Imports: Lean.Elab.Tactic.Grind.Main Lean.Elab.Tactic.Grind.Basic Lean.Elab.Tactic.Grind.BuiltinTactic Lean.Elab.Tactic.Grind.ShowState Lean.Elab.Tactic.Grind.Have Lean.Elab.Tactic.Grind.Trace Lean.Elab.Tactic.Grind.Config Lean.Elab.Tactic.Grind.Lint Lean.Elab.Tactic.Grind.LintExceptions Lean.Elab.Tactic.Grind.Annotated Lean.Elab.Tactic.Grind.Sym Lean.Elab.Tactic.Grind.SimprocDSL Lean.Elab.Tactic.Grind.SimprocDSLBuiltin Lean.Elab.Tactic.Grind.RegisterSymSimp Lean.Elab.Tactic.Grind.DSimprocDSL Lean.Elab.Tactic.Grind.DSimprocDSLBuiltin Lean.Elab.Tactic.Grind.RegisterSymDSimp
use crate::r#gen::Lean::Elab::Tactic::Grind::Annotated::{
    initialize_Lean_Elab_Tactic_Grind_Annotated,
    runtime_initialize_Lean_Elab_Tactic_Grind_Annotated,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Basic::{
    initialize_Lean_Elab_Tactic_Grind_Basic, runtime_initialize_Lean_Elab_Tactic_Grind_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::BuiltinTactic::{
    initialize_Lean_Elab_Tactic_Grind_BuiltinTactic,
    runtime_initialize_Lean_Elab_Tactic_Grind_BuiltinTactic,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Config::{
    initialize_Lean_Elab_Tactic_Grind_Config, runtime_initialize_Lean_Elab_Tactic_Grind_Config,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::DSimprocDSL::{
    initialize_Lean_Elab_Tactic_Grind_DSimprocDSL,
    runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::DSimprocDSLBuiltin::{
    initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin,
    runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Have::{
    initialize_Lean_Elab_Tactic_Grind_Have, runtime_initialize_Lean_Elab_Tactic_Grind_Have,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Lint::{
    initialize_Lean_Elab_Tactic_Grind_Lint, runtime_initialize_Lean_Elab_Tactic_Grind_Lint,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::LintExceptions::{
    initialize_Lean_Elab_Tactic_Grind_LintExceptions,
    runtime_initialize_Lean_Elab_Tactic_Grind_LintExceptions,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Main::{
    initialize_Lean_Elab_Tactic_Grind_Main, runtime_initialize_Lean_Elab_Tactic_Grind_Main,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::RegisterSymDSimp::{
    initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp,
    runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::RegisterSymSimp::{
    initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp,
    runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::ShowState::{
    initialize_Lean_Elab_Tactic_Grind_ShowState,
    runtime_initialize_Lean_Elab_Tactic_Grind_ShowState,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::SimprocDSL::{
    initialize_Lean_Elab_Tactic_Grind_SimprocDSL,
    runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::SimprocDSLBuiltin::{
    initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin,
    runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Sym::{
    initialize_Lean_Elab_Tactic_Grind_Sym, runtime_initialize_Lean_Elab_Tactic_Grind_Sym,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::Trace::{
    initialize_Lean_Elab_Tactic_Grind_Trace, runtime_initialize_Lean_Elab_Tactic_Grind_Trace,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_BuiltinTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_LintExceptions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Grind(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Grind_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_BuiltinTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_ShowState(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Trace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Lint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_LintExceptions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Annotated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_SimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_SimprocDSLBuiltin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_RegisterSymSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_DSimprocDSL(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_DSimprocDSLBuiltin(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind_RegisterSymDSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind(builtin);
}
