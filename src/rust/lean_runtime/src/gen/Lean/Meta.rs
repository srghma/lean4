// Lean compiler output
// Module: Lean.Meta
// Imports: Lean.Meta.Basic Lean.Meta.HasAssignableMVar Lean.Meta.LevelDefEq Lean.Meta.WHNF Lean.Meta.InferType Lean.Meta.FunInfo Lean.Meta.ExprDefEq Lean.Meta.DecLevel Lean.Meta.DiscrTree Lean.Meta.Reduce Lean.Meta.Instances Lean.Meta.AbstractMVars Lean.Meta.SynthInstance Lean.Meta.AppBuilder Lean.Meta.Sorry Lean.Meta.Tactic Lean.Meta.KAbstract Lean.Meta.RecursorInfo Lean.Meta.GeneralizeTelescope Lean.Meta.Match Lean.Meta.ReduceEval Lean.Meta.Closure Lean.Meta.AbstractNestedProofs Lean.Meta.WrapInstance Lean.Meta.LetToHave Lean.Meta.ForEachExpr Lean.Meta.Transform Lean.Meta.PPGoal Lean.Meta.UnificationHint Lean.Meta.Inductive Lean.Meta.SizeOf Lean.Meta.IndPredBelow Lean.Meta.Coe Lean.Meta.CollectFVars Lean.Meta.GeneralizeVars Lean.Meta.Injective Lean.Meta.Structure Lean.Meta.Constructions Lean.Meta.CongrTheorems Lean.Meta.Eqns Lean.Meta.ExprLens Lean.Meta.ExprTraverse Lean.Meta.Eval Lean.Meta.CoeAttr Lean.Meta.Iterator Lean.Meta.LazyDiscrTree Lean.Meta.LitValues Lean.Meta.CheckTactic Lean.Meta.Canonicalizer Lean.Meta.Diagnostics Lean.Meta.BinderNameHint Lean.Meta.TryThis Lean.Meta.Hint Lean.Meta.MethodSpecs Lean.Meta.CtorIdxHInj Lean.Meta.Sym Lean.Meta.MonadSimp Lean.Meta.HaveTelescope
use crate::r#gen::Lean::Meta::AbstractMVars::{
    initialize_Lean_Meta_AbstractMVars, runtime_initialize_Lean_Meta_AbstractMVars,
};
use crate::r#gen::Lean::Meta::AbstractNestedProofs::{
    initialize_Lean_Meta_AbstractNestedProofs, runtime_initialize_Lean_Meta_AbstractNestedProofs,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::BinderNameHint::{
    initialize_Lean_Meta_BinderNameHint, runtime_initialize_Lean_Meta_BinderNameHint,
};
use crate::r#gen::Lean::Meta::Canonicalizer::{
    initialize_Lean_Meta_Canonicalizer, runtime_initialize_Lean_Meta_Canonicalizer,
};
use crate::r#gen::Lean::Meta::CheckTactic::{
    initialize_Lean_Meta_CheckTactic, runtime_initialize_Lean_Meta_CheckTactic,
};
use crate::r#gen::Lean::Meta::Closure::{
    initialize_Lean_Meta_Closure, runtime_initialize_Lean_Meta_Closure,
};
use crate::r#gen::Lean::Meta::Coe::{initialize_Lean_Meta_Coe, runtime_initialize_Lean_Meta_Coe};
use crate::r#gen::Lean::Meta::CoeAttr::{
    initialize_Lean_Meta_CoeAttr, runtime_initialize_Lean_Meta_CoeAttr,
};
use crate::r#gen::Lean::Meta::CollectFVars::{
    initialize_Lean_Meta_CollectFVars, runtime_initialize_Lean_Meta_CollectFVars,
};
use crate::r#gen::Lean::Meta::CongrTheorems::{
    initialize_Lean_Meta_CongrTheorems, runtime_initialize_Lean_Meta_CongrTheorems,
};
use crate::r#gen::Lean::Meta::Constructions::{
    initialize_Lean_Meta_Constructions, runtime_initialize_Lean_Meta_Constructions,
};
use crate::r#gen::Lean::Meta::CtorIdxHInj::{
    initialize_Lean_Meta_CtorIdxHInj, runtime_initialize_Lean_Meta_CtorIdxHInj,
};
use crate::r#gen::Lean::Meta::DecLevel::{
    initialize_Lean_Meta_DecLevel, runtime_initialize_Lean_Meta_DecLevel,
};
use crate::r#gen::Lean::Meta::Diagnostics::{
    initialize_Lean_Meta_Diagnostics, runtime_initialize_Lean_Meta_Diagnostics,
};
use crate::r#gen::Lean::Meta::DiscrTree::{
    initialize_Lean_Meta_DiscrTree, runtime_initialize_Lean_Meta_DiscrTree,
};
use crate::r#gen::Lean::Meta::Eqns::{
    initialize_Lean_Meta_Eqns, runtime_initialize_Lean_Meta_Eqns,
};
use crate::r#gen::Lean::Meta::Eval::{
    initialize_Lean_Meta_Eval, runtime_initialize_Lean_Meta_Eval,
};
use crate::r#gen::Lean::Meta::ExprDefEq::{
    initialize_Lean_Meta_ExprDefEq, runtime_initialize_Lean_Meta_ExprDefEq,
};
use crate::r#gen::Lean::Meta::ExprLens::{
    initialize_Lean_Meta_ExprLens, runtime_initialize_Lean_Meta_ExprLens,
};
use crate::r#gen::Lean::Meta::ExprTraverse::{
    initialize_Lean_Meta_ExprTraverse, runtime_initialize_Lean_Meta_ExprTraverse,
};
use crate::r#gen::Lean::Meta::ForEachExpr::{
    initialize_Lean_Meta_ForEachExpr, runtime_initialize_Lean_Meta_ForEachExpr,
};
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, runtime_initialize_Lean_Meta_FunInfo,
};
use crate::r#gen::Lean::Meta::GeneralizeTelescope::{
    initialize_Lean_Meta_GeneralizeTelescope, runtime_initialize_Lean_Meta_GeneralizeTelescope,
};
use crate::r#gen::Lean::Meta::GeneralizeVars::{
    initialize_Lean_Meta_GeneralizeVars, runtime_initialize_Lean_Meta_GeneralizeVars,
};
use crate::r#gen::Lean::Meta::HasAssignableMVar::{
    initialize_Lean_Meta_HasAssignableMVar, runtime_initialize_Lean_Meta_HasAssignableMVar,
};
use crate::r#gen::Lean::Meta::HaveTelescope::{
    initialize_Lean_Meta_HaveTelescope, runtime_initialize_Lean_Meta_HaveTelescope,
};
use crate::r#gen::Lean::Meta::Hint::{
    initialize_Lean_Meta_Hint, runtime_initialize_Lean_Meta_Hint,
};
use crate::r#gen::Lean::Meta::IndPredBelow::{
    initialize_Lean_Meta_IndPredBelow, runtime_initialize_Lean_Meta_IndPredBelow,
};
use crate::r#gen::Lean::Meta::Inductive::{
    initialize_Lean_Meta_Inductive, runtime_initialize_Lean_Meta_Inductive,
};
use crate::r#gen::Lean::Meta::InferType::{
    initialize_Lean_Meta_InferType, runtime_initialize_Lean_Meta_InferType,
};
use crate::r#gen::Lean::Meta::Injective::{
    initialize_Lean_Meta_Injective, runtime_initialize_Lean_Meta_Injective,
};
use crate::r#gen::Lean::Meta::Instances::{
    initialize_Lean_Meta_Instances, runtime_initialize_Lean_Meta_Instances,
};
use crate::r#gen::Lean::Meta::Iterator::{
    initialize_Lean_Meta_Iterator, runtime_initialize_Lean_Meta_Iterator,
};
use crate::r#gen::Lean::Meta::KAbstract::{
    initialize_Lean_Meta_KAbstract, runtime_initialize_Lean_Meta_KAbstract,
};
use crate::r#gen::Lean::Meta::LazyDiscrTree::{
    initialize_Lean_Meta_LazyDiscrTree, runtime_initialize_Lean_Meta_LazyDiscrTree,
};
use crate::r#gen::Lean::Meta::LetToHave::{
    initialize_Lean_Meta_LetToHave, runtime_initialize_Lean_Meta_LetToHave,
};
use crate::r#gen::Lean::Meta::LevelDefEq::{
    initialize_Lean_Meta_LevelDefEq, runtime_initialize_Lean_Meta_LevelDefEq,
};
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::Meta::Match::{
    initialize_Lean_Meta_Match, runtime_initialize_Lean_Meta_Match,
};
use crate::r#gen::Lean::Meta::MethodSpecs::{
    initialize_Lean_Meta_MethodSpecs, runtime_initialize_Lean_Meta_MethodSpecs,
};
use crate::r#gen::Lean::Meta::MonadSimp::{
    initialize_Lean_Meta_MonadSimp, runtime_initialize_Lean_Meta_MonadSimp,
};
use crate::r#gen::Lean::Meta::PPGoal::{
    initialize_Lean_Meta_PPGoal, runtime_initialize_Lean_Meta_PPGoal,
};
use crate::r#gen::Lean::Meta::RecursorInfo::{
    initialize_Lean_Meta_RecursorInfo, runtime_initialize_Lean_Meta_RecursorInfo,
};
use crate::r#gen::Lean::Meta::Reduce::{
    initialize_Lean_Meta_Reduce, runtime_initialize_Lean_Meta_Reduce,
};
use crate::r#gen::Lean::Meta::ReduceEval::{
    initialize_Lean_Meta_ReduceEval, runtime_initialize_Lean_Meta_ReduceEval,
};
use crate::r#gen::Lean::Meta::SizeOf::{
    initialize_Lean_Meta_SizeOf, runtime_initialize_Lean_Meta_SizeOf,
};
use crate::r#gen::Lean::Meta::Sorry::{
    initialize_Lean_Meta_Sorry, runtime_initialize_Lean_Meta_Sorry,
};
use crate::r#gen::Lean::Meta::Structure::{
    initialize_Lean_Meta_Structure, runtime_initialize_Lean_Meta_Structure,
};
use crate::r#gen::Lean::Meta::Sym::{initialize_Lean_Meta_Sym, runtime_initialize_Lean_Meta_Sym};
use crate::r#gen::Lean::Meta::SynthInstance::{
    initialize_Lean_Meta_SynthInstance, runtime_initialize_Lean_Meta_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::{
    initialize_Lean_Meta_Tactic, runtime_initialize_Lean_Meta_Tactic,
};
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
use crate::r#gen::Lean::Meta::TryThis::{
    initialize_Lean_Meta_TryThis, runtime_initialize_Lean_Meta_TryThis,
};
use crate::r#gen::Lean::Meta::UnificationHint::{
    initialize_Lean_Meta_UnificationHint, runtime_initialize_Lean_Meta_UnificationHint,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::Meta::WrapInstance::{
    initialize_Lean_Meta_WrapInstance, runtime_initialize_Lean_Meta_WrapInstance,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HasAssignableMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LevelDefEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ExprDefEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AbstractMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_KAbstract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_RecursorInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_GeneralizeTelescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ReduceEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AbstractNestedProofs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WrapInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LetToHave(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_UnificationHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Inductive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IndPredBelow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CollectFVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_GeneralizeVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CongrTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ExprLens(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_ExprTraverse(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CoeAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LazyDiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CheckTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_BinderNameHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Hint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MethodSpecs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorIdxHInj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MonadSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_HaveTelescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_HasAssignableMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_LevelDefEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ExprDefEq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_DiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Instances(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AbstractMVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sorry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_KAbstract(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_RecursorInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_GeneralizeTelescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Match(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ReduceEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AbstractNestedProofs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_WrapInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_LetToHave(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ForEachExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_UnificationHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Inductive(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_SizeOf(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_IndPredBelow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CollectFVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_GeneralizeVars(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Structure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CongrTheorems(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Eqns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ExprLens(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_ExprTraverse(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Eval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CoeAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Iterator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_LazyDiscrTree(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CheckTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Canonicalizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Diagnostics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_BinderNameHint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_TryThis(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Hint(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_MethodSpecs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorIdxHInj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_MonadSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_HaveTelescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta(builtin);
}
