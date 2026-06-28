// Lean compiler output
// Module: Lean.Compiler.LCNF
// Imports: Lean.Compiler.LCNF.AlphaEqv Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.Check Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.CSE Lean.Compiler.LCNF.DependsOn Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.FixedParams Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.JoinPoints Lean.Compiler.LCNF.LCtx Lean.Compiler.LCNF.Level Lean.Compiler.LCNF.Main Lean.Compiler.LCNF.Passes Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.PullFunDecls Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.Specialize Lean.Compiler.LCNF.SpecInfo Lean.Compiler.LCNF.ToDecl Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.ToLCNF Lean.Compiler.LCNF.Types Lean.Compiler.LCNF.Util Lean.Compiler.LCNF.ConfigOptions Lean.Compiler.LCNF.MonoTypes Lean.Compiler.LCNF.ToMono Lean.Compiler.LCNF.MonadScope Lean.Compiler.LCNF.Closure Lean.Compiler.LCNF.LambdaLifting Lean.Compiler.LCNF.ReduceArity Lean.Compiler.LCNF.Probing Lean.Compiler.LCNF.Irrelevant Lean.Compiler.LCNF.SplitSCC
use crate::r#gen::Lean::Compiler::LCNF::AlphaEqv::{
    initialize_Lean_Compiler_LCNF_AlphaEqv, runtime_initialize_Lean_Compiler_LCNF_AlphaEqv,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Compiler::LCNF::Bind::{
    initialize_Lean_Compiler_LCNF_Bind, runtime_initialize_Lean_Compiler_LCNF_Bind,
};
use crate::r#gen::Lean::Compiler::LCNF::CSE::{
    initialize_Lean_Compiler_LCNF_CSE, runtime_initialize_Lean_Compiler_LCNF_CSE,
};
use crate::r#gen::Lean::Compiler::LCNF::Check::{
    initialize_Lean_Compiler_LCNF_Check, runtime_initialize_Lean_Compiler_LCNF_Check,
};
use crate::r#gen::Lean::Compiler::LCNF::Closure::{
    initialize_Lean_Compiler_LCNF_Closure, runtime_initialize_Lean_Compiler_LCNF_Closure,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    initialize_Lean_Compiler_LCNF_CompilerM, runtime_initialize_Lean_Compiler_LCNF_CompilerM,
};
use crate::r#gen::Lean::Compiler::LCNF::ConfigOptions::{
    initialize_Lean_Compiler_LCNF_ConfigOptions,
    runtime_initialize_Lean_Compiler_LCNF_ConfigOptions,
};
use crate::r#gen::Lean::Compiler::LCNF::DependsOn::{
    initialize_Lean_Compiler_LCNF_DependsOn, runtime_initialize_Lean_Compiler_LCNF_DependsOn,
};
use crate::r#gen::Lean::Compiler::LCNF::ElimDead::{
    initialize_Lean_Compiler_LCNF_ElimDead, runtime_initialize_Lean_Compiler_LCNF_ElimDead,
};
use crate::r#gen::Lean::Compiler::LCNF::FixedParams::{
    initialize_Lean_Compiler_LCNF_FixedParams, runtime_initialize_Lean_Compiler_LCNF_FixedParams,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    initialize_Lean_Compiler_LCNF_InferType, runtime_initialize_Lean_Compiler_LCNF_InferType,
};
use crate::r#gen::Lean::Compiler::LCNF::Irrelevant::{
    initialize_Lean_Compiler_LCNF_Irrelevant, runtime_initialize_Lean_Compiler_LCNF_Irrelevant,
};
use crate::r#gen::Lean::Compiler::LCNF::JoinPoints::{
    initialize_Lean_Compiler_LCNF_JoinPoints, runtime_initialize_Lean_Compiler_LCNF_JoinPoints,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::{
    initialize_Lean_Compiler_LCNF_LCtx, runtime_initialize_Lean_Compiler_LCNF_LCtx,
};
use crate::r#gen::Lean::Compiler::LCNF::LambdaLifting::{
    initialize_Lean_Compiler_LCNF_LambdaLifting,
    runtime_initialize_Lean_Compiler_LCNF_LambdaLifting,
};
use crate::r#gen::Lean::Compiler::LCNF::Level::{
    initialize_Lean_Compiler_LCNF_Level, runtime_initialize_Lean_Compiler_LCNF_Level,
};
use crate::r#gen::Lean::Compiler::LCNF::Main::{
    initialize_Lean_Compiler_LCNF_Main, runtime_initialize_Lean_Compiler_LCNF_Main,
};
use crate::r#gen::Lean::Compiler::LCNF::MonadScope::{
    initialize_Lean_Compiler_LCNF_MonadScope, runtime_initialize_Lean_Compiler_LCNF_MonadScope,
};
use crate::r#gen::Lean::Compiler::LCNF::MonoTypes::{
    initialize_Lean_Compiler_LCNF_MonoTypes, runtime_initialize_Lean_Compiler_LCNF_MonoTypes,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    initialize_Lean_Compiler_LCNF_PassManager, runtime_initialize_Lean_Compiler_LCNF_PassManager,
};
use crate::r#gen::Lean::Compiler::LCNF::Passes::{
    initialize_Lean_Compiler_LCNF_Passes, runtime_initialize_Lean_Compiler_LCNF_Passes,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    initialize_Lean_Compiler_LCNF_PhaseExt, runtime_initialize_Lean_Compiler_LCNF_PhaseExt,
};
use crate::r#gen::Lean::Compiler::LCNF::PrettyPrinter::{
    initialize_Lean_Compiler_LCNF_PrettyPrinter,
    runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter,
};
use crate::r#gen::Lean::Compiler::LCNF::Probing::{
    initialize_Lean_Compiler_LCNF_Probing, runtime_initialize_Lean_Compiler_LCNF_Probing,
};
use crate::r#gen::Lean::Compiler::LCNF::PullFunDecls::{
    initialize_Lean_Compiler_LCNF_PullFunDecls, runtime_initialize_Lean_Compiler_LCNF_PullFunDecls,
};
use crate::r#gen::Lean::Compiler::LCNF::PullLetDecls::{
    initialize_Lean_Compiler_LCNF_PullLetDecls, runtime_initialize_Lean_Compiler_LCNF_PullLetDecls,
};
use crate::r#gen::Lean::Compiler::LCNF::ReduceArity::{
    initialize_Lean_Compiler_LCNF_ReduceArity, runtime_initialize_Lean_Compiler_LCNF_ReduceArity,
};
use crate::r#gen::Lean::Compiler::LCNF::ReduceJpArity::{
    initialize_Lean_Compiler_LCNF_ReduceJpArity,
    runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::{
    initialize_Lean_Compiler_LCNF_Simp, runtime_initialize_Lean_Compiler_LCNF_Simp,
};
use crate::r#gen::Lean::Compiler::LCNF::SpecInfo::{
    initialize_Lean_Compiler_LCNF_SpecInfo, runtime_initialize_Lean_Compiler_LCNF_SpecInfo,
};
use crate::r#gen::Lean::Compiler::LCNF::Specialize::{
    initialize_Lean_Compiler_LCNF_Specialize, runtime_initialize_Lean_Compiler_LCNF_Specialize,
};
use crate::r#gen::Lean::Compiler::LCNF::SplitSCC::{
    initialize_Lean_Compiler_LCNF_SplitSCC, runtime_initialize_Lean_Compiler_LCNF_SplitSCC,
};
use crate::r#gen::Lean::Compiler::LCNF::ToDecl::{
    initialize_Lean_Compiler_LCNF_ToDecl, runtime_initialize_Lean_Compiler_LCNF_ToDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::ToExpr::{
    initialize_Lean_Compiler_LCNF_ToExpr, runtime_initialize_Lean_Compiler_LCNF_ToExpr,
};
use crate::r#gen::Lean::Compiler::LCNF::ToLCNF::{
    initialize_Lean_Compiler_LCNF_ToLCNF, runtime_initialize_Lean_Compiler_LCNF_ToLCNF,
};
use crate::r#gen::Lean::Compiler::LCNF::ToMono::{
    initialize_Lean_Compiler_LCNF_ToMono, runtime_initialize_Lean_Compiler_LCNF_ToMono,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    initialize_Lean_Compiler_LCNF_Types, runtime_initialize_Lean_Compiler_LCNF_Types,
};
use crate::r#gen::Lean::Compiler::LCNF::Util::{
    initialize_Lean_Compiler_LCNF_Util, runtime_initialize_Lean_Compiler_LCNF_Util,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Bind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CSE(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_JoinPoints(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Passes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Specialize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToMono(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Closure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Probing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SplitSCC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Bind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CompilerM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CSE(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_FixedParams(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_JoinPoints(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_LCtx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Passes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PassManager(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PullFunDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Specialize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_SpecInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToDecl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ConfigOptions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonoTypes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToMono(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_MonadScope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Closure(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Probing(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Irrelevant(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_SplitSCC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF(builtin);
}
