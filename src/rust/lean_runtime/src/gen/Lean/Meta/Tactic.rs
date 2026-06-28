// Lean compiler output
// Module: Lean.Meta.Tactic
// Imports: Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Contradiction Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Generalize Lean.Meta.Tactic.Replace Lean.Meta.Tactic.Lets Lean.Meta.Tactic.Induction Lean.Meta.Tactic.Cases Lean.Meta.Tactic.ElimInfo Lean.Meta.Tactic.Delta Lean.Meta.Tactic.Constructor Lean.Meta.Tactic.Simp Lean.Meta.Tactic.AuxLemma Lean.Meta.Tactic.SplitIf Lean.Meta.Tactic.Split Lean.Meta.Tactic.TryThis Lean.Meta.Tactic.Cleanup Lean.Meta.Tactic.Unfold Lean.Meta.Tactic.Rename Lean.Meta.Tactic.AC Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Congr Lean.Meta.Tactic.Repeat Lean.Meta.Tactic.NormCast Lean.Meta.Tactic.IndependentOf Lean.Meta.Tactic.Symm Lean.Meta.Tactic.Backtrack Lean.Meta.Tactic.SolveByElim Lean.Meta.Tactic.FunInd Lean.Meta.Tactic.Rfl Lean.Meta.Tactic.Rewrites Lean.Meta.Tactic.Grind Lean.Meta.Tactic.Ext Lean.Meta.Tactic.Try Lean.Meta.Tactic.Cbv Lean.Meta.Tactic.BVDecide
use crate::r#gen::Lean::Meta::Tactic::AC::{
    initialize_Lean_Meta_Tactic_AC, runtime_initialize_Lean_Meta_Tactic_AC,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::{
    initialize_Lean_Meta_Tactic_Apply, runtime_initialize_Lean_Meta_Tactic_Apply,
};
use crate::r#gen::Lean::Meta::Tactic::Assert::{
    initialize_Lean_Meta_Tactic_Assert, runtime_initialize_Lean_Meta_Tactic_Assert,
};
use crate::r#gen::Lean::Meta::Tactic::Assumption::{
    initialize_Lean_Meta_Tactic_Assumption, runtime_initialize_Lean_Meta_Tactic_Assumption,
};
use crate::r#gen::Lean::Meta::Tactic::AuxLemma::{
    initialize_Lean_Meta_Tactic_AuxLemma, runtime_initialize_Lean_Meta_Tactic_AuxLemma,
};
use crate::r#gen::Lean::Meta::Tactic::BVDecide::{
    initialize_Lean_Meta_Tactic_BVDecide, runtime_initialize_Lean_Meta_Tactic_BVDecide,
};
use crate::r#gen::Lean::Meta::Tactic::Backtrack::{
    initialize_Lean_Meta_Tactic_Backtrack, runtime_initialize_Lean_Meta_Tactic_Backtrack,
};
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    initialize_Lean_Meta_Tactic_Cases, runtime_initialize_Lean_Meta_Tactic_Cases,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::{
    initialize_Lean_Meta_Tactic_Cbv, runtime_initialize_Lean_Meta_Tactic_Cbv,
};
use crate::r#gen::Lean::Meta::Tactic::Cleanup::{
    initialize_Lean_Meta_Tactic_Cleanup, runtime_initialize_Lean_Meta_Tactic_Cleanup,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::{
    initialize_Lean_Meta_Tactic_Clear, runtime_initialize_Lean_Meta_Tactic_Clear,
};
use crate::r#gen::Lean::Meta::Tactic::Congr::{
    initialize_Lean_Meta_Tactic_Congr, runtime_initialize_Lean_Meta_Tactic_Congr,
};
use crate::r#gen::Lean::Meta::Tactic::Constructor::{
    initialize_Lean_Meta_Tactic_Constructor, runtime_initialize_Lean_Meta_Tactic_Constructor,
};
use crate::r#gen::Lean::Meta::Tactic::Contradiction::{
    initialize_Lean_Meta_Tactic_Contradiction, runtime_initialize_Lean_Meta_Tactic_Contradiction,
};
use crate::r#gen::Lean::Meta::Tactic::Delta::{
    initialize_Lean_Meta_Tactic_Delta, runtime_initialize_Lean_Meta_Tactic_Delta,
};
use crate::r#gen::Lean::Meta::Tactic::ElimInfo::{
    initialize_Lean_Meta_Tactic_ElimInfo, runtime_initialize_Lean_Meta_Tactic_ElimInfo,
};
use crate::r#gen::Lean::Meta::Tactic::Ext::{
    initialize_Lean_Meta_Tactic_Ext, runtime_initialize_Lean_Meta_Tactic_Ext,
};
use crate::r#gen::Lean::Meta::Tactic::FunInd::{
    initialize_Lean_Meta_Tactic_FunInd, runtime_initialize_Lean_Meta_Tactic_FunInd,
};
use crate::r#gen::Lean::Meta::Tactic::Generalize::{
    initialize_Lean_Meta_Tactic_Generalize, runtime_initialize_Lean_Meta_Tactic_Generalize,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::{
    initialize_Lean_Meta_Tactic_Grind, runtime_initialize_Lean_Meta_Tactic_Grind,
};
use crate::r#gen::Lean::Meta::Tactic::IndependentOf::{
    initialize_Lean_Meta_Tactic_IndependentOf, runtime_initialize_Lean_Meta_Tactic_IndependentOf,
};
use crate::r#gen::Lean::Meta::Tactic::Induction::{
    initialize_Lean_Meta_Tactic_Induction, runtime_initialize_Lean_Meta_Tactic_Induction,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{
    initialize_Lean_Meta_Tactic_Intro, runtime_initialize_Lean_Meta_Tactic_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Lets::{
    initialize_Lean_Meta_Tactic_Lets, runtime_initialize_Lean_Meta_Tactic_Lets,
};
use crate::r#gen::Lean::Meta::Tactic::NormCast::{
    initialize_Lean_Meta_Tactic_NormCast, runtime_initialize_Lean_Meta_Tactic_NormCast,
};
use crate::r#gen::Lean::Meta::Tactic::Refl::{
    initialize_Lean_Meta_Tactic_Refl, runtime_initialize_Lean_Meta_Tactic_Refl,
};
use crate::r#gen::Lean::Meta::Tactic::Rename::{
    initialize_Lean_Meta_Tactic_Rename, runtime_initialize_Lean_Meta_Tactic_Rename,
};
use crate::r#gen::Lean::Meta::Tactic::Repeat::{
    initialize_Lean_Meta_Tactic_Repeat, runtime_initialize_Lean_Meta_Tactic_Repeat,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    initialize_Lean_Meta_Tactic_Replace, runtime_initialize_Lean_Meta_Tactic_Replace,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::{
    initialize_Lean_Meta_Tactic_Revert, runtime_initialize_Lean_Meta_Tactic_Revert,
};
use crate::r#gen::Lean::Meta::Tactic::Rewrite::{
    initialize_Lean_Meta_Tactic_Rewrite, runtime_initialize_Lean_Meta_Tactic_Rewrite,
};
use crate::r#gen::Lean::Meta::Tactic::Rewrites::{
    initialize_Lean_Meta_Tactic_Rewrites, runtime_initialize_Lean_Meta_Tactic_Rewrites,
};
use crate::r#gen::Lean::Meta::Tactic::Rfl::{
    initialize_Lean_Meta_Tactic_Rfl, runtime_initialize_Lean_Meta_Tactic_Rfl,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::{
    initialize_Lean_Meta_Tactic_Simp, runtime_initialize_Lean_Meta_Tactic_Simp,
};
use crate::r#gen::Lean::Meta::Tactic::SolveByElim::{
    initialize_Lean_Meta_Tactic_SolveByElim, runtime_initialize_Lean_Meta_Tactic_SolveByElim,
};
use crate::r#gen::Lean::Meta::Tactic::Split::{
    initialize_Lean_Meta_Tactic_Split, runtime_initialize_Lean_Meta_Tactic_Split,
};
use crate::r#gen::Lean::Meta::Tactic::SplitIf::{
    initialize_Lean_Meta_Tactic_SplitIf, runtime_initialize_Lean_Meta_Tactic_SplitIf,
};
use crate::r#gen::Lean::Meta::Tactic::Symm::{
    initialize_Lean_Meta_Tactic_Symm, runtime_initialize_Lean_Meta_Tactic_Symm,
};
use crate::r#gen::Lean::Meta::Tactic::Try::{
    initialize_Lean_Meta_Tactic_Try, runtime_initialize_Lean_Meta_Tactic_Try,
};
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::Meta::Tactic::Unfold::{
    initialize_Lean_Meta_Tactic_Unfold, runtime_initialize_Lean_Meta_Tactic_Unfold,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Generalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Induction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_ElimInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_SplitIf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Congr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_NormCast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_IndependentOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Backtrack(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunInd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Rewrites(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Try(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_BVDecide(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assumption(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Contradiction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Assert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rewrite(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Generalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Replace(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Lets(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Induction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_ElimInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Delta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Constructor(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_SplitIf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Unfold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rename(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Refl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Congr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Repeat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_NormCast(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_IndependentOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Symm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Backtrack(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_SolveByElim(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_FunInd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rfl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Rewrites(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Ext(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Try(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_BVDecide(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic(builtin);
}
