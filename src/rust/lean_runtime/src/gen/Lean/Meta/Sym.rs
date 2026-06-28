// Lean compiler output
// Module: Lean.Meta.Sym
// Imports: Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.AlphaShareCommon Lean.Meta.Sym.ExprPtr Lean.Meta.Sym.SymM Lean.Meta.Sym.MaxFVar Lean.Meta.Sym.ReplaceS Lean.Meta.Sym.LooseBVarsS Lean.Meta.Sym.InstantiateS Lean.Meta.Sym.IsClass Lean.Meta.Sym.Intro Lean.Meta.Sym.InstantiateMVarsS Lean.Meta.Sym.ProofInstInfo Lean.Meta.Sym.AbstractS Lean.Meta.Sym.Pattern Lean.Meta.Sym.Apply Lean.Meta.Sym.InferType Lean.Meta.Sym.Simp Lean.Meta.Sym.DSimp Lean.Meta.Sym.Util Lean.Meta.Sym.Eta Lean.Meta.Sym.Canon Lean.Meta.Sym.Arith Lean.Meta.Sym.Grind Lean.Meta.Sym.SynthInstance
use crate::r#gen::Lean::Meta::Sym::AbstractS::{
    initialize_Lean_Meta_Sym_AbstractS, runtime_initialize_Lean_Meta_Sym_AbstractS,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareCommon::{
    initialize_Lean_Meta_Sym_AlphaShareCommon, runtime_initialize_Lean_Meta_Sym_AlphaShareCommon,
};
use crate::r#gen::Lean::Meta::Sym::Apply::{
    initialize_Lean_Meta_Sym_Apply, runtime_initialize_Lean_Meta_Sym_Apply,
};
use crate::r#gen::Lean::Meta::Sym::Arith::{
    initialize_Lean_Meta_Sym_Arith, runtime_initialize_Lean_Meta_Sym_Arith,
};
use crate::r#gen::Lean::Meta::Sym::Canon::{
    initialize_Lean_Meta_Sym_Canon, runtime_initialize_Lean_Meta_Sym_Canon,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::{
    initialize_Lean_Meta_Sym_DSimp, runtime_initialize_Lean_Meta_Sym_DSimp,
};
use crate::r#gen::Lean::Meta::Sym::Eta::{
    initialize_Lean_Meta_Sym_Eta, runtime_initialize_Lean_Meta_Sym_Eta,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    initialize_Lean_Meta_Sym_ExprPtr, runtime_initialize_Lean_Meta_Sym_ExprPtr,
};
use crate::r#gen::Lean::Meta::Sym::Grind::{
    initialize_Lean_Meta_Sym_Grind, runtime_initialize_Lean_Meta_Sym_Grind,
};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateMVarsS::{
    initialize_Lean_Meta_Sym_InstantiateMVarsS, runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
use crate::r#gen::Lean::Meta::Sym::Intro::{
    initialize_Lean_Meta_Sym_Intro, runtime_initialize_Lean_Meta_Sym_Intro,
};
use crate::r#gen::Lean::Meta::Sym::IsClass::{
    initialize_Lean_Meta_Sym_IsClass, runtime_initialize_Lean_Meta_Sym_IsClass,
};
use crate::r#gen::Lean::Meta::Sym::LooseBVarsS::{
    initialize_Lean_Meta_Sym_LooseBVarsS, runtime_initialize_Lean_Meta_Sym_LooseBVarsS,
};
use crate::r#gen::Lean::Meta::Sym::MaxFVar::{
    initialize_Lean_Meta_Sym_MaxFVar, runtime_initialize_Lean_Meta_Sym_MaxFVar,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::{
    initialize_Lean_Meta_Sym_Pattern, runtime_initialize_Lean_Meta_Sym_Pattern,
};
use crate::r#gen::Lean::Meta::Sym::ProofInstInfo::{
    initialize_Lean_Meta_Sym_ProofInstInfo, runtime_initialize_Lean_Meta_Sym_ProofInstInfo,
};
use crate::r#gen::Lean::Meta::Sym::ReplaceS::{
    initialize_Lean_Meta_Sym_ReplaceS, runtime_initialize_Lean_Meta_Sym_ReplaceS,
};
use crate::r#gen::Lean::Meta::Sym::Simp::{
    initialize_Lean_Meta_Sym_Simp, runtime_initialize_Lean_Meta_Sym_Simp,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::{
    initialize_Lean_Meta_Sym_SynthInstance, runtime_initialize_Lean_Meta_Sym_SynthInstance,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_MaxFVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareCommon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_MaxFVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ReplaceS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_LooseBVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_IsClass(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateMVarsS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AbstractS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Apply(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_DSimp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Eta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Canon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Grind(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym(builtin);
}
