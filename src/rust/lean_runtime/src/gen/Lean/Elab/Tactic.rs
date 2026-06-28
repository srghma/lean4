// Lean compiler output
// Module: Lean.Elab.Tactic
// Imports: Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Induction Lean.Elab.Tactic.Generalize Lean.Elab.Tactic.Injection Lean.Elab.Tactic.Match Lean.Elab.Tactic.Rewrite Lean.Elab.Tactic.Location Lean.Elab.Tactic.SimpTrace Lean.Elab.Tactic.Simp Lean.Elab.Tactic.Simproc Lean.Elab.Tactic.CbvSimproc Lean.Elab.Tactic.BuiltinTactic Lean.Elab.Tactic.Split Lean.Elab.Tactic.Conv Lean.Elab.Tactic.Delta Lean.Elab.Tactic.Meta Lean.Elab.Tactic.Unfold Lean.Elab.Tactic.Calc Lean.Elab.Tactic.Congr Lean.Elab.Tactic.Guard Lean.Elab.Tactic.RCases Lean.Elab.Tactic.Repeat Lean.Elab.Tactic.Ext Lean.Elab.Tactic.Change Lean.Elab.Tactic.FalseOrByContra Lean.Elab.Tactic.Omega Lean.Elab.Tactic.Simpa Lean.Elab.Tactic.NormCast Lean.Elab.Tactic.Symm Lean.Elab.Tactic.SolveByElim Lean.Elab.Tactic.LibrarySearch Lean.Elab.Tactic.ShowTerm Lean.Elab.Tactic.Rfl Lean.Elab.Tactic.Rewrites Lean.Elab.Tactic.DiscrTreeKey Lean.Elab.Tactic.BVDecide Lean.Elab.Tactic.BoolToPropSimps Lean.Elab.Tactic.Classical Lean.Elab.Tactic.Impossible Lean.Elab.Tactic.Grind Lean.Elab.Tactic.Monotonicity Lean.Elab.Tactic.Try Lean.Elab.Tactic.AsAuxLemma Lean.Elab.Tactic.TreeTacAttr Lean.Elab.Tactic.ExposeNames Lean.Elab.Tactic.SimpArith Lean.Elab.Tactic.Show Lean.Elab.Tactic.Lets Lean.Elab.Tactic.Do Lean.Elab.Tactic.Decide Lean.Elab.Tactic.Cbv
use crate::r#gen::Lean::Elab::Tactic::AsAuxLemma::{
    initialize_Lean_Elab_Tactic_AsAuxLemma, runtime_initialize_Lean_Elab_Tactic_AsAuxLemma,
};
use crate::r#gen::Lean::Elab::Tactic::BVDecide::{
    initialize_Lean_Elab_Tactic_BVDecide, runtime_initialize_Lean_Elab_Tactic_BVDecide,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::BoolToPropSimps::{
    initialize_Lean_Elab_Tactic_BoolToPropSimps,
    runtime_initialize_Lean_Elab_Tactic_BoolToPropSimps,
};
use crate::r#gen::Lean::Elab::Tactic::BuiltinTactic::{
    initialize_Lean_Elab_Tactic_BuiltinTactic, runtime_initialize_Lean_Elab_Tactic_BuiltinTactic,
};
use crate::r#gen::Lean::Elab::Tactic::Calc::{
    initialize_Lean_Elab_Tactic_Calc, runtime_initialize_Lean_Elab_Tactic_Calc,
};
use crate::r#gen::Lean::Elab::Tactic::Cbv::{
    initialize_Lean_Elab_Tactic_Cbv, runtime_initialize_Lean_Elab_Tactic_Cbv,
};
use crate::r#gen::Lean::Elab::Tactic::CbvSimproc::{
    initialize_Lean_Elab_Tactic_CbvSimproc, runtime_initialize_Lean_Elab_Tactic_CbvSimproc,
};
use crate::r#gen::Lean::Elab::Tactic::Change::{
    initialize_Lean_Elab_Tactic_Change, runtime_initialize_Lean_Elab_Tactic_Change,
};
use crate::r#gen::Lean::Elab::Tactic::Classical::{
    initialize_Lean_Elab_Tactic_Classical, runtime_initialize_Lean_Elab_Tactic_Classical,
};
use crate::r#gen::Lean::Elab::Tactic::Congr::{
    initialize_Lean_Elab_Tactic_Congr, runtime_initialize_Lean_Elab_Tactic_Congr,
};
use crate::r#gen::Lean::Elab::Tactic::Conv::{
    initialize_Lean_Elab_Tactic_Conv, runtime_initialize_Lean_Elab_Tactic_Conv,
};
use crate::r#gen::Lean::Elab::Tactic::Decide::{
    initialize_Lean_Elab_Tactic_Decide, runtime_initialize_Lean_Elab_Tactic_Decide,
};
use crate::r#gen::Lean::Elab::Tactic::Delta::{
    initialize_Lean_Elab_Tactic_Delta, runtime_initialize_Lean_Elab_Tactic_Delta,
};
use crate::r#gen::Lean::Elab::Tactic::DiscrTreeKey::{
    initialize_Lean_Elab_Tactic_DiscrTreeKey, runtime_initialize_Lean_Elab_Tactic_DiscrTreeKey,
};
use crate::r#gen::Lean::Elab::Tactic::Do::{
    initialize_Lean_Elab_Tactic_Do, runtime_initialize_Lean_Elab_Tactic_Do,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Elab::Tactic::ExposeNames::{
    initialize_Lean_Elab_Tactic_ExposeNames, runtime_initialize_Lean_Elab_Tactic_ExposeNames,
};
use crate::r#gen::Lean::Elab::Tactic::Ext::{
    initialize_Lean_Elab_Tactic_Ext, runtime_initialize_Lean_Elab_Tactic_Ext,
};
use crate::r#gen::Lean::Elab::Tactic::FalseOrByContra::{
    initialize_Lean_Elab_Tactic_FalseOrByContra,
    runtime_initialize_Lean_Elab_Tactic_FalseOrByContra,
};
use crate::r#gen::Lean::Elab::Tactic::Generalize::{
    initialize_Lean_Elab_Tactic_Generalize, runtime_initialize_Lean_Elab_Tactic_Generalize,
};
use crate::r#gen::Lean::Elab::Tactic::Grind::{
    initialize_Lean_Elab_Tactic_Grind, runtime_initialize_Lean_Elab_Tactic_Grind,
};
use crate::r#gen::Lean::Elab::Tactic::Guard::{
    initialize_Lean_Elab_Tactic_Guard, runtime_initialize_Lean_Elab_Tactic_Guard,
};
use crate::r#gen::Lean::Elab::Tactic::Impossible::{
    initialize_Lean_Elab_Tactic_Impossible, runtime_initialize_Lean_Elab_Tactic_Impossible,
};
use crate::r#gen::Lean::Elab::Tactic::Induction::{
    initialize_Lean_Elab_Tactic_Induction, runtime_initialize_Lean_Elab_Tactic_Induction,
};
use crate::r#gen::Lean::Elab::Tactic::Injection::{
    initialize_Lean_Elab_Tactic_Injection, runtime_initialize_Lean_Elab_Tactic_Injection,
};
use crate::r#gen::Lean::Elab::Tactic::Lets::{
    initialize_Lean_Elab_Tactic_Lets, runtime_initialize_Lean_Elab_Tactic_Lets,
};
use crate::r#gen::Lean::Elab::Tactic::LibrarySearch::{
    initialize_Lean_Elab_Tactic_LibrarySearch, runtime_initialize_Lean_Elab_Tactic_LibrarySearch,
};
use crate::r#gen::Lean::Elab::Tactic::Location::{
    initialize_Lean_Elab_Tactic_Location, runtime_initialize_Lean_Elab_Tactic_Location,
};
use crate::r#gen::Lean::Elab::Tactic::Match::{
    initialize_Lean_Elab_Tactic_Match, runtime_initialize_Lean_Elab_Tactic_Match,
};
use crate::r#gen::Lean::Elab::Tactic::Meta::{
    initialize_Lean_Elab_Tactic_Meta, runtime_initialize_Lean_Elab_Tactic_Meta,
};
use crate::r#gen::Lean::Elab::Tactic::Monotonicity::{
    initialize_Lean_Elab_Tactic_Monotonicity, runtime_initialize_Lean_Elab_Tactic_Monotonicity,
};
use crate::r#gen::Lean::Elab::Tactic::NormCast::{
    initialize_Lean_Elab_Tactic_NormCast, runtime_initialize_Lean_Elab_Tactic_NormCast,
};
use crate::r#gen::Lean::Elab::Tactic::Omega::{
    initialize_Lean_Elab_Tactic_Omega, runtime_initialize_Lean_Elab_Tactic_Omega,
};
use crate::r#gen::Lean::Elab::Tactic::RCases::{
    initialize_Lean_Elab_Tactic_RCases, runtime_initialize_Lean_Elab_Tactic_RCases,
};
use crate::r#gen::Lean::Elab::Tactic::Repeat::{
    initialize_Lean_Elab_Tactic_Repeat, runtime_initialize_Lean_Elab_Tactic_Repeat,
};
use crate::r#gen::Lean::Elab::Tactic::Rewrite::{
    initialize_Lean_Elab_Tactic_Rewrite, runtime_initialize_Lean_Elab_Tactic_Rewrite,
};
use crate::r#gen::Lean::Elab::Tactic::Rewrites::{
    initialize_Lean_Elab_Tactic_Rewrites, runtime_initialize_Lean_Elab_Tactic_Rewrites,
};
use crate::r#gen::Lean::Elab::Tactic::Rfl::{
    initialize_Lean_Elab_Tactic_Rfl, runtime_initialize_Lean_Elab_Tactic_Rfl,
};
use crate::r#gen::Lean::Elab::Tactic::Show::{
    initialize_Lean_Elab_Tactic_Show, runtime_initialize_Lean_Elab_Tactic_Show,
};
use crate::r#gen::Lean::Elab::Tactic::ShowTerm::{
    initialize_Lean_Elab_Tactic_ShowTerm, runtime_initialize_Lean_Elab_Tactic_ShowTerm,
};
use crate::r#gen::Lean::Elab::Tactic::Simp::{
    initialize_Lean_Elab_Tactic_Simp, runtime_initialize_Lean_Elab_Tactic_Simp,
};
use crate::r#gen::Lean::Elab::Tactic::SimpArith::{
    initialize_Lean_Elab_Tactic_SimpArith, runtime_initialize_Lean_Elab_Tactic_SimpArith,
};
use crate::r#gen::Lean::Elab::Tactic::SimpTrace::{
    initialize_Lean_Elab_Tactic_SimpTrace, runtime_initialize_Lean_Elab_Tactic_SimpTrace,
};
use crate::r#gen::Lean::Elab::Tactic::Simpa::{
    initialize_Lean_Elab_Tactic_Simpa, runtime_initialize_Lean_Elab_Tactic_Simpa,
};
use crate::r#gen::Lean::Elab::Tactic::Simproc::{
    initialize_Lean_Elab_Tactic_Simproc, runtime_initialize_Lean_Elab_Tactic_Simproc,
};
use crate::r#gen::Lean::Elab::Tactic::SolveByElim::{
    initialize_Lean_Elab_Tactic_SolveByElim, runtime_initialize_Lean_Elab_Tactic_SolveByElim,
};
use crate::r#gen::Lean::Elab::Tactic::Split::{
    initialize_Lean_Elab_Tactic_Split, runtime_initialize_Lean_Elab_Tactic_Split,
};
use crate::r#gen::Lean::Elab::Tactic::Symm::{
    initialize_Lean_Elab_Tactic_Symm, runtime_initialize_Lean_Elab_Tactic_Symm,
};
use crate::r#gen::Lean::Elab::Tactic::TreeTacAttr::{
    initialize_Lean_Elab_Tactic_TreeTacAttr, runtime_initialize_Lean_Elab_Tactic_TreeTacAttr,
};
use crate::r#gen::Lean::Elab::Tactic::Try::{
    initialize_Lean_Elab_Tactic_Try, runtime_initialize_Lean_Elab_Tactic_Try,
};
use crate::r#gen::Lean::Elab::Tactic::Unfold::{
    initialize_Lean_Elab_Tactic_Unfold, runtime_initialize_Lean_Elab_Tactic_Unfold,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Conv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Delta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Congr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Guard(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simpa(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_NormCast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Symm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_SolveByElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ShowTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Rewrites(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Impossible(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Monotonicity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Try(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_TreeTacAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ExposeNames(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_SimpArith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Show(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Lets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Decide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Cbv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Generalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Rewrite(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Location(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_SimpTrace(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_BuiltinTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Conv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Delta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Calc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Congr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Guard(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_RCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Repeat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Change(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_FalseOrByContra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Simpa(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_NormCast(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Symm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_SolveByElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ShowTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Rfl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Rewrites(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_BVDecide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Impossible(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Monotonicity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Try(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_TreeTacAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ExposeNames(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_SimpArith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Show(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Lets(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Decide(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Cbv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic(builtin);
}
