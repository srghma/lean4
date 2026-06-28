// Lean compiler output
// Module: Lean.Meta.Sym.Simp
// Imports: Lean.Meta.Sym.Simp.App Lean.Meta.Sym.Simp.CongrInfo Lean.Meta.Sym.Simp.DiscrTree Lean.Meta.Sym.Simp.Main Lean.Meta.Sym.Simp.Result Lean.Meta.Sym.Simp.Rewrite Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.Simp.Simproc Lean.Meta.Sym.Simp.Theorems Lean.Meta.Sym.Simp.Have Lean.Meta.Sym.Simp.Lambda Lean.Meta.Sym.Simp.Forall Lean.Meta.Sym.Simp.Debug Lean.Meta.Sym.Simp.EvalGround Lean.Meta.Sym.Simp.Discharger Lean.Meta.Sym.Simp.ControlFlow Lean.Meta.Sym.Simp.Goal Lean.Meta.Sym.Simp.Telescope Lean.Meta.Sym.Simp.Attr Lean.Meta.Sym.Simp.Variant Lean.Meta.Sym.Simp.RegisterCommand
use crate::r#gen::Lean::Meta::Sym::Simp::App::{
    initialize_Lean_Meta_Sym_Simp_App, runtime_initialize_Lean_Meta_Sym_Simp_App,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Attr::{
    initialize_Lean_Meta_Sym_Simp_Attr, runtime_initialize_Lean_Meta_Sym_Simp_Attr,
};
use crate::r#gen::Lean::Meta::Sym::Simp::CongrInfo::{
    initialize_Lean_Meta_Sym_Simp_CongrInfo, runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo,
};
use crate::r#gen::Lean::Meta::Sym::Simp::ControlFlow::{
    initialize_Lean_Meta_Sym_Simp_ControlFlow, runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Debug::{
    initialize_Lean_Meta_Sym_Simp_Debug, runtime_initialize_Lean_Meta_Sym_Simp_Debug,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Discharger::{
    initialize_Lean_Meta_Sym_Simp_Discharger, runtime_initialize_Lean_Meta_Sym_Simp_Discharger,
};
use crate::r#gen::Lean::Meta::Sym::Simp::DiscrTree::{
    initialize_Lean_Meta_Sym_Simp_DiscrTree, runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree,
};
use crate::r#gen::Lean::Meta::Sym::Simp::EvalGround::{
    initialize_Lean_Meta_Sym_Simp_EvalGround, runtime_initialize_Lean_Meta_Sym_Simp_EvalGround,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Forall::{
    initialize_Lean_Meta_Sym_Simp_Forall, runtime_initialize_Lean_Meta_Sym_Simp_Forall,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Goal::{
    initialize_Lean_Meta_Sym_Simp_Goal, runtime_initialize_Lean_Meta_Sym_Simp_Goal,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Have::{
    initialize_Lean_Meta_Sym_Simp_Have, runtime_initialize_Lean_Meta_Sym_Simp_Have,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Lambda::{
    initialize_Lean_Meta_Sym_Simp_Lambda, runtime_initialize_Lean_Meta_Sym_Simp_Lambda,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Main::{
    initialize_Lean_Meta_Sym_Simp_Main, runtime_initialize_Lean_Meta_Sym_Simp_Main,
};
use crate::r#gen::Lean::Meta::Sym::Simp::RegisterCommand::{
    initialize_Lean_Meta_Sym_Simp_RegisterCommand,
    runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Result::{
    initialize_Lean_Meta_Sym_Simp_Result, runtime_initialize_Lean_Meta_Sym_Simp_Result,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Rewrite::{
    initialize_Lean_Meta_Sym_Simp_Rewrite, runtime_initialize_Lean_Meta_Sym_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Simproc::{
    initialize_Lean_Meta_Sym_Simp_Simproc, runtime_initialize_Lean_Meta_Sym_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Telescope::{
    initialize_Lean_Meta_Sym_Simp_Telescope, runtime_initialize_Lean_Meta_Sym_Simp_Telescope,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    initialize_Lean_Meta_Sym_Simp_Theorems, runtime_initialize_Lean_Meta_Sym_Simp_Theorems,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Variant::{
    initialize_Lean_Meta_Sym_Simp_Variant, runtime_initialize_Lean_Meta_Sym_Simp_Variant,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Debug(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_App(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_CongrInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Have(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Lambda(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Debug(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_EvalGround(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Discharger(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Goal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Variant(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_RegisterCommand(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Simp(builtin);
}
