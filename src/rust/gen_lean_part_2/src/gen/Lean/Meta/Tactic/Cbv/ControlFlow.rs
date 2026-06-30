// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.ControlFlow
// Imports: Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.Simp.Result Lean.Meta.Sym.Simp.Rewrite Lean.Meta.Sym.Simp.ControlFlow Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.InstantiateS Lean.Meta.Sym.InferType Lean.Meta.Sym.Simp.App Lean.Meta.SynthInstance Lean.Meta.WHNF Lean.Meta.AppBuilder Init.Sym.Lemmas Lean.Meta.Tactic.Cbv.TheoremsLookup Lean.Meta.Tactic.Cbv.Opaque Lean.Meta.Tactic.Cbv.CbvEvalExt Lean.Compiler.NoncomputableAttr Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt, lean_nat_sub,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_sym_simp, lean_usize_add,
    lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::CbvSimproc::{
    initialize_Init_CbvSimproc, runtime_initialize_Init_CbvSimproc,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::MetaTypes::l_Lean_Meta_instBEqTransparencyMode_beq;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_Name_mkStr3};
use crate::r#gen::Init::Sym::Lemmas::{
    initialize_Init_Sym_Lemmas, runtime_initialize_Init_Sym_Lemmas,
};
use crate::r#gen::Lean::Compiler::NoncomputableAttr::{
    initialize_Lean_Compiler_NoncomputableAttr, l_Lean_isNoncomputable, l_Lean_noncomputableExt,
    runtime_initialize_Lean_Compiler_NoncomputableAttr,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_name;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_betaRev,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_constLevels_x21, l_Lean_Expr_constName_x3f,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_getBoundedAppFn,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_replaceFn, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkApp6, l_Lean_mkApp8, l_Lean_mkBVar, l_Lean_mkConst, l_Lean_mkLambda,
    l_Lean_mkNot,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkOfEqFalseCore, l_Lean_Meta_mkOfEqTrueCore,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::l_Lean_Meta_Match_Extension_getMatcherInfo_x3f;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::InferType::{
    initialize_Lean_Meta_Sym_InferType, l_Lean_Meta_Sym_mkEqRefl___redArg,
    runtime_initialize_Lean_Meta_Sym_InferType,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
use crate::r#gen::Lean::Meta::Sym::Simp::App::{
    initialize_Lean_Meta_Sym_Simp_App, l_Lean_Meta_Sym_Simp_propagateOverApplied,
    l_Lean_Meta_Sym_Simp_simpAppArgRange, l_Lean_Meta_Sym_Simp_simpInterlaced,
    runtime_initialize_Lean_Meta_Sym_Simp_App,
};
use crate::r#gen::Lean::Meta::Sym::Simp::ControlFlow::{
    initialize_Lean_Meta_Sym_Simp_ControlFlow, l_Lean_Meta_Sym_Simp_simpCond,
    l_Lean_Meta_Sym_Simp_simpCond___boxed, runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Discharger::l_Lean_Meta_Sym_Simp_dischargeNone___boxed;
use crate::r#gen::Lean::Meta::Sym::Simp::Result::{
    initialize_Lean_Meta_Sym_Simp_Result, l_Lean_Meta_Sym_Simp_mkEqTrans___redArg,
    runtime_initialize_Lean_Meta_Sym_Simp_Result,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Rewrite::{
    initialize_Lean_Meta_Sym_Simp_Rewrite, l_Lean_Meta_Sym_Simp_Theorems_rewrite,
    runtime_initialize_Lean_Meta_Sym_Simp_Rewrite,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, l_Lean_Meta_Sym_Simp_Result_withContextDependent,
    l_Lean_Meta_Sym_Simp_mkRflResult, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getBoolFalseExpr___redArg, l_Lean_Meta_Sym_getBoolTrueExpr___redArg,
    l_Lean_Meta_Sym_isFalseExpr___redArg, l_Lean_Meta_Sym_isTrueExpr___redArg,
    l_Lean_Meta_Sym_shareCommon___redArg, l_Lean_Meta_Sym_shareCommonInc___redArg,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    initialize_Lean_Meta_SynthInstance, l_Lean_Meta_trySynthInstance,
    runtime_initialize_Lean_Meta_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::CbvEvalExt::{
    initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt, l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg,
    runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::CbvSimproc::{
    initialize_Lean_Meta_Tactic_Cbv_CbvSimproc, l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr,
    l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc,
    runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::Opaque::{
    initialize_Lean_Meta_Tactic_Cbv_Opaque, l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg,
    runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque,
};
use crate::r#gen::Lean::Meta::Tactic::Cbv::TheoremsLookup::{
    initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup, l_Lean_Meta_Tactic_Cbv_getMatchTheorems,
    runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_reduceRecMatcher_x3f___boxed,
    runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::ReducibilityAttrs::{
    l_Lean_instBEqReducibilityStatus_beq, lean_get_reducibility_status,
};
use crate::r#gen::Lean::Util::FoldConsts::l_Lean_Expr_getUsedConstants;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value) as *mut leanh::LeanObject,4342836574150310743 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 115, 70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value) as *mut leanh::LeanObject,4342836574150310743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__0_value) as *mut leanh::LeanObject,14734865452941588245 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 115, 84, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value) as *mut leanh::LeanObject,4342836574150310743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__2_value) as *mut leanh::LeanObject,83052734847462153 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 121, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 116, 101, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value) as *mut leanh::LeanObject,12871497013927706280 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 116, 101, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value) as *mut leanh::LeanObject,17775442772636682853 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 116, 101, 95, 116, 114, 117, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__0_value) as *mut leanh::LeanObject,6416865616034892810 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 116, 101, 95, 102, 97, 108, 115, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__2_value) as *mut leanh::LeanObject,2184043267806764676 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 116, 101, 95, 99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__0_value) as *mut leanh::LeanObject,6903251136980284309 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__0_value) as *mut leanh::LeanObject,18356704233129443855 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__8_value) as *mut leanh::LeanObject,2772357888408479705 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__6_value) as *mut leanh::LeanObject,7092435127666596636 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [100, 101, 99, 105, 100, 97, 98, 108, 101, 95, 111, 102, 95, 100, 101, 99, 105, 100, 97, 98, 108, 101, 95, 111, 102, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__4_value) as *mut leanh::LeanObject,8254948630024697980 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__7_value) as *mut leanh::LeanObject,15684782314253460228 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__9_value) as *mut leanh::LeanObject,7490975742882862809 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,16489734963670585437 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 111, 110, 116, 114, 111, 108, 70, 108, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__9_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,14509854243239906201 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__10_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,7047804931116776700 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__11_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,15746103376134014109 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__12_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,18291473563994198517 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,18142236484849173136 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__14_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__15_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,3992815600722207868 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 105, 109, 112, 73, 116, 101, 67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__17_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,7647868492020377930 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1_value) as *mut leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value: leanh::LeanArrayObject<6> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__19_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [100, 105, 116, 101, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value) as *mut leanh::LeanObject,16431606950389960653 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 105, 116, 101, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value) as *mut leanh::LeanObject,135770998913847834 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 112, 114, 95, 112, 114, 111, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__1_value) as *mut leanh::LeanObject,15841710565803995561 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [100, 105, 116, 101, 95, 116, 114, 117, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__4_value) as *mut leanh::LeanObject,13686543964022880632 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [109, 112, 114, 95, 110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__0_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__6_value) as *mut leanh::LeanObject,13082247772038117497 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [100, 105, 116, 101, 95, 102, 97, 108, 115, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__9_value) as *mut leanh::LeanObject,1817535296476228808 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__0_value) as *mut leanh::LeanObject,8738205681931236784 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__3_value) as *mut leanh::LeanObject,3329307374202973768 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [100, 105, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__0_value) as *mut leanh::LeanObject,8391571994004792969 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [110, 111, 116, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__2_value) as *mut leanh::LeanObject,9941313967319291291 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__2_value) as *mut leanh::LeanObject,557460064797095758 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 110, 116, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__7_value) as *mut leanh::LeanObject,11870096045526947150 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__8_value) as *mut leanh::LeanObject,18067798339771668657 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__0_value) as *mut leanh::LeanObject,15199346438430382657 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__13_value) as *mut leanh::LeanObject,15303888708270464921 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [100, 105, 116, 101, 95, 99, 111, 110, 100, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__15_value) as *mut leanh::LeanObject,187051596005140493 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 105, 109, 112, 68, 73, 116, 101, 67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value) as *mut leanh::LeanObject,2502323639553915582 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1_value) as *mut leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value: leanh::LeanArrayObject<6> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 105, 100, 101, 95, 105, 115, 84, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__0_value) as *mut leanh::LeanObject,5725272028696080000 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [100, 101, 99, 105, 100, 101, 95, 105, 115, 70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__3_value) as *mut leanh::LeanObject,9785197008526531870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [100, 101, 99, 105, 100, 101, 95, 105, 115, 84, 114, 117, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__0_value) as *mut leanh::LeanObject,11410008614811545252 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [100, 101, 99, 105, 100, 101, 95, 105, 115, 70, 97, 108, 115, 101, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__3_value) as *mut leanh::LeanObject,17618178609125420242 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 103, 114, 95, 115, 105, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value) as *mut leanh::LeanObject,4342836574150310743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0_value) as *mut leanh::LeanObject,15998082856370921488 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 101, 99, 105, 100, 101, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__2_value) as *mut leanh::LeanObject,6455497336075398727 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 105, 100, 101, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__5_value) as *mut leanh::LeanObject,7571348278136080589 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [100, 101, 99, 105, 100, 101, 95, 112, 114, 111, 112, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__9_value) as *mut leanh::LeanObject,15541540937362108983 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [100, 101, 99, 105, 100, 101, 95, 112, 114, 111, 112, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__4_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__5_value) as *mut leanh::LeanObject,3782814055319769887 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__12_value) as *mut leanh::LeanObject,11791201806532295003 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 105, 109, 112, 68, 101, 99, 105, 100, 101, 67, 98, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__16_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value) as *mut leanh::LeanObject,6894368808693124723 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1_value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value: leanh::LeanArrayObject<3> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_simpCond___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__13_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,15338332981773714252 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,13378427860974793246 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [115, 105, 109, 112, 67, 98, 118, 67, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject,7103057750393062815 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 111, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject,105488867511536770 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__6_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value: leanh::LeanArrayObject<4> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__7_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [99, 98, 118, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [114, 101, 119, 114, 105, 116, 101, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value)
            as *mut leanh::LeanObject,
        9691683737394756276 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__1_value)
            as *mut leanh::LeanObject,
        15200645332484307630 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [116, 114, 97, 99, 101, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__3_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [114, 101, 99, 77, 97, 116, 99, 104, 101, 114, 58, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [10, 61, 61, 62, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0_value: leanh::LeanArrayObject<5> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*5) as u16, other: 0, tag: 246 }, m_size: 5, m_capacity: 5, m_data: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 105, 109, 112, 68, 101, 99, 105, 100, 97, 98, 108, 101, 82, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject,14230692633960002640 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0_value) as *mut leanh::LeanObject,4342836574150310743 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__2_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject,10995968517338862238 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject,((( 5 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value: leanh::LeanArrayObject<6> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Sym_Simp_dischargeNone___boxed as *const core::ffi::c_void, m_arity: 11, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [99, 111, 110, 116, 114, 111, 108, 70, 108, 111, 119, 0],
    };
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16__value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__0_value)
                as *mut leanh::LeanObject,
            9691683737394756276 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__0_value)
                as *mut leanh::LeanObject,
            957843270380816252 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [109, 97, 116, 99, 104, 32, 96, 0],
    };
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [96, 58, 0],
    };
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(
    mut v_p_3570_: *mut leanh::LeanObject,
    mut v_a_3571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3577_: u8 = 0;
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: u8 = 0;
    let mut v___x_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: u8 = 0;
    let mut v___x_3589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3593_: u8 = 0;
    let mut v_a_3594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3597_: u8 = 0;
    let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3573_ =
                    l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_p_3570_, v_a_3571_);
                if leanh::lean_obj_tag(v___x_3573_) == 0 {
                    v_a_3574_ = leanh::lean_ctor_get(v___x_3573_, 0);
                    v_isSharedCheck_3593_ = (!leanh::lean_is_exclusive(v___x_3573_)) as u8;
                    if v_isSharedCheck_3593_ == 0 {
                        v___x_3576_ = v___x_3573_;
                        v_isShared_3577_ = v_isSharedCheck_3593_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3574_);
                        leanh::lean_dec(v___x_3573_);
                        v___x_3576_ = leanh::lean_box(0);
                        v_isShared_3577_ = v_isSharedCheck_3593_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_p_3570_);
                    v_a_3594_ = leanh::lean_ctor_get(v___x_3573_, 0);
                    v_isSharedCheck_3601_ = (!leanh::lean_is_exclusive(v___x_3573_)) as u8;
                    if v_isSharedCheck_3601_ == 0 {
                        v___x_3596_ = v___x_3573_;
                        v_isShared_3597_ = v_isSharedCheck_3601_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3594_);
                        leanh::lean_dec(v___x_3573_);
                        v___x_3596_ = leanh::lean_box(0);
                        v_isShared_3597_ = v_isSharedCheck_3601_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3578_ = lean_st_ref_get(v_a_3571_);
                if leanh::lean_obj_tag(v_a_3574_) == 0 {
                    v_env_3579_ = leanh::lean_ctor_get(v___x_3578_, 0);
                    leanh::lean_inc_ref(v_env_3579_);
                    leanh::lean_dec(v___x_3578_);
                    v___x_3580_ = l_Lean_noncomputableExt;
                    v_toEnvExtension_3581_ = leanh::lean_ctor_get(v___x_3580_, 0);
                    v_asyncMode_3582_ = leanh::lean_ctor_get(v_toEnvExtension_3581_, 2);
                    v___x_3583_ = l_Lean_isNoncomputable(v_env_3579_, v_p_3570_, v_asyncMode_3582_);
                    v___x_3584_ = leanh::lean_box((v___x_3583_) as usize);
                    if v_isShared_3577_ == 0 {
                        leanh::lean_ctor_set(v___x_3576_, 0, v___x_3584_);
                        v___x_3586_ = v___x_3576_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3587_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3587_, 0, v___x_3584_);
                        v___x_3586_ = v_reuseFailAlloc_3587_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_3574_, 1);
                    leanh::lean_dec(v___x_3578_);
                    leanh::lean_dec(v_p_3570_);
                    v___x_3588_ = 0;
                    v___x_3589_ = leanh::lean_box((v___x_3588_) as usize);
                    if v_isShared_3577_ == 0 {
                        leanh::lean_ctor_set(v___x_3576_, 0, v___x_3589_);
                        v___x_3591_ = v___x_3576_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3592_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
                        v___x_3591_ = v_reuseFailAlloc_3592_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3586_;
            }
            3 => {
                return v___x_3591_;
            }
            4 => {
                if v_isShared_3597_ == 0 {
                    v___x_3599_ = v___x_3596_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
                    v___x_3599_ = v_reuseFailAlloc_3600_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg___boxed(
    mut v_p_3602_: *mut leanh::LeanObject,
    mut v_a_3603_: *mut leanh::LeanObject,
    mut v_a_3604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3605_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(v_p_3602_, v_a_3603_);
    leanh::lean_dec(v_a_3603_);
    return v_res_3605_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(
    mut v_p_3606_: *mut leanh::LeanObject,
    mut v_a_3607_: *mut leanh::LeanObject,
    mut v_a_3608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3610_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(v_p_3606_, v_a_3608_);
    return v___x_3610_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___boxed(
    mut v_p_3611_: *mut leanh::LeanObject,
    mut v_a_3612_: *mut leanh::LeanObject,
    mut v_a_3613_: *mut leanh::LeanObject,
    mut v_a_3614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3615_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable(
            v_p_3611_, v_a_3612_, v_a_3613_,
        );
    leanh::lean_dec(v_a_3613_);
    leanh::lean_dec_ref(v_a_3612_);
    return v_res_3615_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(
    mut v_as_3616_: *mut leanh::LeanObject,
    mut v_i_3617_: usize,
    mut v_stop_3618_: usize,
    mut v___y_3619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3621_: u8 = 0;
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___x_3628_: u8 = 0;
    let mut v___x_3629_: usize = 0;
    let mut v___x_3630_: usize = 0;
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3635_: u8 = 0;
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3621_ = lean_usize_dec_eq(v_i_3617_, v_stop_3618_);
                if v___x_3621_ == 0 {
                    v___x_3622_ = lean_array_uget_borrowed(v_as_3616_, v_i_3617_);
                    leanh::lean_inc(v___x_3622_);
                    v___x_3623_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_isCbvNoncomputable___redArg(v___x_3622_, v___y_3619_);
                    if leanh::lean_obj_tag(v___x_3623_) == 0 {
                        v_a_3624_ = leanh::lean_ctor_get(v___x_3623_, 0);
                        v_isSharedCheck_3635_ =
                            (!leanh::lean_is_exclusive(v___x_3623_)) as u8;
                        if v_isSharedCheck_3635_ == 0 {
                            v___x_3626_ = v___x_3623_;
                            v_isShared_3627_ = v_isSharedCheck_3635_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3624_);
                            leanh::lean_dec(v___x_3623_);
                            v___x_3626_ = leanh::lean_box(0);
                            v_isShared_3627_ = v_isSharedCheck_3635_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3623_;
                    }
                } else {
                    v___x_3636_ = 0;
                    v___x_3637_ = leanh::lean_box((v___x_3636_) as usize);
                    v___x_3638_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3638_, 0, v___x_3637_);
                    return v___x_3638_;
                }
            }
            1 => {
                v___x_3628_ = (leanh::lean_unbox(v_a_3624_) as u8);
                if v___x_3628_ == 0 {
                    leanh::lean_del_object(v___x_3626_);
                    leanh::lean_dec(v_a_3624_);
                    v___x_3629_ = 1usize;
                    v___x_3630_ = lean_usize_add(v_i_3617_, v___x_3629_);
                    v_i_3617_ = v___x_3630_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_3627_ == 0 {
                        v___x_3633_ = v___x_3626_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3624_);
                        v___x_3633_ = v_reuseFailAlloc_3634_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg___boxed(
    mut v_as_3639_: *mut leanh::LeanObject,
    mut v_i_3640_: *mut leanh::LeanObject,
    mut v_stop_3641_: *mut leanh::LeanObject,
    mut v___y_3642_: *mut leanh::LeanObject,
    mut v___y_3643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3644_: usize = 0;
    let mut v_stop_boxed_3645_: usize = 0;
    let mut v_res_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3644_ = leanh::lean_unbox_usize(v_i_3640_);
    leanh::lean_dec(v_i_3640_);
    v_stop_boxed_3645_ = leanh::lean_unbox_usize(v_stop_3641_);
    leanh::lean_dec(v_stop_3641_);
    v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v_as_3639_, v_i_boxed_3644_, v_stop_boxed_3645_, v___y_3642_);
    leanh::lean_dec(v___y_3642_);
    leanh::lean_dec_ref(v_as_3639_);
    return v_res_3646_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3650_ = leanh::lean_box(0);
    v___x_3651_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__1;
    v___x_3652_ = l_Lean_mkConst(v___x_3651_, v___x_3650_);
    return v___x_3652_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(
    mut v_p_3653_: *mut leanh::LeanObject,
    mut v_a_3654_: *mut leanh::LeanObject,
    mut v_a_3655_: *mut leanh::LeanObject,
    mut v_a_3656_: *mut leanh::LeanObject,
    mut v_a_3657_: *mut leanh::LeanObject,
    mut v_a_3658_: *mut leanh::LeanObject,
    mut v_a_3659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3668_: u8 = 0;
    let mut v_a_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3672_: u8 = 0;
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3678_: u8 = 0;
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3685_: u8 = 0;
    let mut v_a_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: u8 = 0;
    let mut v___x_3698_: usize = 0;
    let mut v___x_3699_: usize = 0;
    let mut v___x_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___x_3705_: u8 = 0;
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut v_a_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3713_: u8 = 0;
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3717_: u8 = 0;
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3722_: u8 = 0;
    let mut v_a_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3726_: u8 = 0;
    let mut v___x_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3661_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__2);
                v___x_3662_ = l_Lean_Expr_app___override(v___x_3661_, v_p_3653_);
                v___x_3663_ = leanh::lean_box(0);
                v___x_3664_ = l_Lean_Meta_trySynthInstance(
                    v___x_3662_,
                    v___x_3663_,
                    v_a_3656_,
                    v_a_3657_,
                    v_a_3658_,
                    v_a_3659_,
                );
                if leanh::lean_obj_tag(v___x_3664_) == 0 {
                    v_a_3665_ = leanh::lean_ctor_get(v___x_3664_, 0);
                    v_isSharedCheck_3722_ = (!leanh::lean_is_exclusive(v___x_3664_)) as u8;
                    if v_isSharedCheck_3722_ == 0 {
                        v___x_3667_ = v___x_3664_;
                        v_isShared_3668_ = v_isSharedCheck_3722_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3665_);
                        leanh::lean_dec(v___x_3664_);
                        v___x_3667_ = leanh::lean_box(0);
                        v_isShared_3668_ = v_isSharedCheck_3722_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3723_ = leanh::lean_ctor_get(v___x_3664_, 0);
                    v_isSharedCheck_3730_ = (!leanh::lean_is_exclusive(v___x_3664_)) as u8;
                    if v_isSharedCheck_3730_ == 0 {
                        v___x_3725_ = v___x_3664_;
                        v_isShared_3726_ = v_isSharedCheck_3730_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3723_);
                        leanh::lean_dec(v___x_3664_);
                        v___x_3725_ = leanh::lean_box(0);
                        v_isShared_3726_ = v_isSharedCheck_3730_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_3665_) == 1 {
                    leanh::lean_del_object(v___x_3667_);
                    v_a_3669_ = leanh::lean_ctor_get(v_a_3665_, 0);
                    v_isSharedCheck_3718_ = (!leanh::lean_is_exclusive(v_a_3665_)) as u8;
                    if v_isSharedCheck_3718_ == 0 {
                        v___x_3671_ = v_a_3665_;
                        v_isShared_3672_ = v_isSharedCheck_3718_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3669_);
                        leanh::lean_dec(v_a_3665_);
                        v___x_3671_ = leanh::lean_box(0);
                        v_isShared_3672_ = v_isSharedCheck_3718_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3665_);
                    if v_isShared_3668_ == 0 {
                        leanh::lean_ctor_set(v___x_3667_, 0, v___x_3663_);
                        v___x_3720_ = v___x_3667_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3721_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3663_);
                        v___x_3720_ = v_reuseFailAlloc_3721_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_a_3669_);
                v___x_3694_ = l_Lean_Expr_getUsedConstants(v_a_3669_);
                v___x_3695_ = leanh::lean_unsigned_to_nat(0);
                v___x_3696_ = lean_array_get_size(v___x_3694_);
                v___x_3697_ = lean_nat_dec_lt(v___x_3695_, v___x_3696_);
                if v___x_3697_ == 0 {
                    leanh::lean_dec_ref(v___x_3694_);
                    state = 3;
                    continue;
                } else {
                    if v___x_3697_ == 0 {
                        leanh::lean_dec_ref(v___x_3694_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3698_ = 0usize;
                        v___x_3699_ = lean_usize_of_nat(v___x_3696_);
                        v___x_3700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v___x_3694_, v___x_3698_, v___x_3699_, v_a_3659_);
                        leanh::lean_dec_ref(v___x_3694_);
                        if leanh::lean_obj_tag(v___x_3700_) == 0 {
                            v_a_3701_ = leanh::lean_ctor_get(v___x_3700_, 0);
                            v_isSharedCheck_3709_ =
                                (!leanh::lean_is_exclusive(v___x_3700_)) as u8;
                            if v_isSharedCheck_3709_ == 0 {
                                v___x_3703_ = v___x_3700_;
                                v_isShared_3704_ = v_isSharedCheck_3709_;
                                state = 9;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3701_);
                                leanh::lean_dec(v___x_3700_);
                                v___x_3703_ = leanh::lean_box(0);
                                v_isShared_3704_ = v_isSharedCheck_3709_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_3671_);
                            leanh::lean_dec(v_a_3669_);
                            v_a_3710_ = leanh::lean_ctor_get(v___x_3700_, 0);
                            v_isSharedCheck_3717_ =
                                (!leanh::lean_is_exclusive(v___x_3700_)) as u8;
                            if v_isSharedCheck_3717_ == 0 {
                                v___x_3712_ = v___x_3700_;
                                v_isShared_3713_ = v_isSharedCheck_3717_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3710_);
                                leanh::lean_dec(v___x_3700_);
                                v___x_3712_ = leanh::lean_box(0);
                                v_isShared_3713_ = v_isSharedCheck_3717_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3674_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3669_, v_a_3655_);
                if leanh::lean_obj_tag(v___x_3674_) == 0 {
                    v_a_3675_ = leanh::lean_ctor_get(v___x_3674_, 0);
                    v_isSharedCheck_3685_ = (!leanh::lean_is_exclusive(v___x_3674_)) as u8;
                    if v_isSharedCheck_3685_ == 0 {
                        v___x_3677_ = v___x_3674_;
                        v_isShared_3678_ = v_isSharedCheck_3685_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3675_);
                        leanh::lean_dec(v___x_3674_);
                        v___x_3677_ = leanh::lean_box(0);
                        v_isShared_3678_ = v_isSharedCheck_3685_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3671_);
                    v_a_3686_ = leanh::lean_ctor_get(v___x_3674_, 0);
                    v_isSharedCheck_3693_ = (!leanh::lean_is_exclusive(v___x_3674_)) as u8;
                    if v_isSharedCheck_3693_ == 0 {
                        v___x_3688_ = v___x_3674_;
                        v_isShared_3689_ = v_isSharedCheck_3693_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3686_);
                        leanh::lean_dec(v___x_3674_);
                        v___x_3688_ = leanh::lean_box(0);
                        v_isShared_3689_ = v_isSharedCheck_3693_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3672_ == 0 {
                    leanh::lean_ctor_set(v___x_3671_, 0, v_a_3675_);
                    v___x_3680_ = v___x_3671_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3684_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3675_);
                    v___x_3680_ = v_reuseFailAlloc_3684_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3678_ == 0 {
                    leanh::lean_ctor_set(v___x_3677_, 0, v___x_3680_);
                    v___x_3682_ = v___x_3677_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3680_);
                    v___x_3682_ = v_reuseFailAlloc_3683_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3682_;
            }
            7 => {
                if v_isShared_3689_ == 0 {
                    v___x_3691_ = v___x_3688_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3691_;
            }
            9 => {
                v___x_3705_ = (leanh::lean_unbox(v_a_3701_) as u8);
                leanh::lean_dec(v_a_3701_);
                if v___x_3705_ == 0 {
                    leanh::lean_del_object(v___x_3703_);
                    state = 3;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_3671_);
                    leanh::lean_dec(v_a_3669_);
                    if v_isShared_3704_ == 0 {
                        leanh::lean_ctor_set(v___x_3703_, 0, v___x_3663_);
                        v___x_3707_ = v___x_3703_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3663_);
                        v___x_3707_ = v_reuseFailAlloc_3708_;
                        state = 10;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_3707_;
            }
            11 => {
                if v_isShared_3713_ == 0 {
                    v___x_3715_ = v___x_3712_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
                    v___x_3715_ = v_reuseFailAlloc_3716_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3715_;
            }
            13 => {
                return v___x_3720_;
            }
            14 => {
                if v_isShared_3726_ == 0 {
                    v___x_3728_ = v___x_3725_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3729_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
                    v___x_3728_ = v_reuseFailAlloc_3729_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___boxed(
    mut v_p_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
    mut v_a_3733_: *mut leanh::LeanObject,
    mut v_a_3734_: *mut leanh::LeanObject,
    mut v_a_3735_: *mut leanh::LeanObject,
    mut v_a_3736_: *mut leanh::LeanObject,
    mut v_a_3737_: *mut leanh::LeanObject,
    mut v_a_3738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3739_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(v_p_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
    leanh::lean_dec(v_a_3737_);
    leanh::lean_dec_ref(v_a_3736_);
    leanh::lean_dec(v_a_3735_);
    leanh::lean_dec_ref(v_a_3734_);
    leanh::lean_dec(v_a_3733_);
    leanh::lean_dec_ref(v_a_3732_);
    return v_res_3739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0(
    mut v_as_3740_: *mut leanh::LeanObject,
    mut v_i_3741_: usize,
    mut v_stop_3742_: usize,
    mut v___y_3743_: *mut leanh::LeanObject,
    mut v___y_3744_: *mut leanh::LeanObject,
    mut v___y_3745_: *mut leanh::LeanObject,
    mut v___y_3746_: *mut leanh::LeanObject,
    mut v___y_3747_: *mut leanh::LeanObject,
    mut v___y_3748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3750_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___redArg(v_as_3740_, v_i_3741_, v_stop_3742_, v___y_3748_);
    return v___x_3750_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0___boxed(
    mut v_as_3751_: *mut leanh::LeanObject,
    mut v_i_3752_: *mut leanh::LeanObject,
    mut v_stop_3753_: *mut leanh::LeanObject,
    mut v___y_3754_: *mut leanh::LeanObject,
    mut v___y_3755_: *mut leanh::LeanObject,
    mut v___y_3756_: *mut leanh::LeanObject,
    mut v___y_3757_: *mut leanh::LeanObject,
    mut v___y_3758_: *mut leanh::LeanObject,
    mut v___y_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3761_: usize = 0;
    let mut v_stop_boxed_3762_: usize = 0;
    let mut v_res_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3761_ = leanh::lean_unbox_usize(v_i_3752_);
    leanh::lean_dec(v_i_3752_);
    v_stop_boxed_3762_ = leanh::lean_unbox_usize(v_stop_3753_);
    leanh::lean_dec(v_stop_3753_);
    v_res_3763_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance_spec__0(v_as_3751_, v_i_boxed_3761_, v_stop_boxed_3762_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_, v___y_3759_);
    leanh::lean_dec(v___y_3759_);
    leanh::lean_dec_ref(v___y_3758_);
    leanh::lean_dec(v___y_3757_);
    leanh::lean_dec_ref(v___y_3756_);
    leanh::lean_dec(v___y_3755_);
    leanh::lean_dec_ref(v___y_3754_);
    leanh::lean_dec_ref(v_as_3751_);
    return v_res_3763_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(
    mut v_f_3784_: *mut leanh::LeanObject,
    mut v_00_u03b1_3785_: *mut leanh::LeanObject,
    mut v_c_3786_: *mut leanh::LeanObject,
    mut v_inst_3787_: *mut leanh::LeanObject,
    mut v_a_3788_: *mut leanh::LeanObject,
    mut v_b_3789_: *mut leanh::LeanObject,
    mut v_instToMatch_3790_: *mut leanh::LeanObject,
    mut v_fallback_3791_: *mut leanh::LeanObject,
    mut v_a_3792_: *mut leanh::LeanObject,
    mut v_a_3793_: *mut leanh::LeanObject,
    mut v_a_3794_: *mut leanh::LeanObject,
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
    mut v_a_3797_: *mut leanh::LeanObject,
    mut v_a_3798_: *mut leanh::LeanObject,
    mut v_a_3799_: *mut leanh::LeanObject,
    mut v_a_3800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: u8 = 0;
    let mut v___x_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: u8 = 0;
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: u8 = 0;
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: u8 = 0;
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3837_: u8 = 0;
    let mut v_a_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3845_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_3790_, v_a_3798_);
                if leanh::lean_obj_tag(v___x_3802_) == 0 {
                    v_a_3803_ = leanh::lean_ctor_get(v___x_3802_, 0);
                    v_isSharedCheck_3837_ = (!leanh::lean_is_exclusive(v___x_3802_)) as u8;
                    if v_isSharedCheck_3837_ == 0 {
                        v___x_3805_ = v___x_3802_;
                        v_isShared_3806_ = v_isSharedCheck_3837_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3803_);
                        leanh::lean_dec(v___x_3802_);
                        v___x_3805_ = leanh::lean_box(0);
                        v_isShared_3806_ = v_isSharedCheck_3837_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_3791_);
                    leanh::lean_dec_ref(v_b_3789_);
                    leanh::lean_dec_ref(v_a_3788_);
                    leanh::lean_dec_ref(v_inst_3787_);
                    leanh::lean_dec_ref(v_c_3786_);
                    leanh::lean_dec_ref(v_00_u03b1_3785_);
                    v_a_3838_ = leanh::lean_ctor_get(v___x_3802_, 0);
                    v_isSharedCheck_3845_ = (!leanh::lean_is_exclusive(v___x_3802_)) as u8;
                    if v_isSharedCheck_3845_ == 0 {
                        v___x_3840_ = v___x_3802_;
                        v_isShared_3841_ = v_isSharedCheck_3845_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3838_);
                        leanh::lean_dec(v___x_3802_);
                        v___x_3840_ = leanh::lean_box(0);
                        v_isShared_3841_ = v_isSharedCheck_3845_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3807_ = l_Lean_Expr_cleanupAnnotations(v_a_3803_);
                v___x_3808_ = l_Lean_Expr_isApp(v___x_3807_);
                if v___x_3808_ == 0 {
                    leanh::lean_dec_ref(v___x_3807_);
                    leanh::lean_del_object(v___x_3805_);
                    leanh::lean_dec_ref(v_b_3789_);
                    leanh::lean_dec_ref(v_a_3788_);
                    leanh::lean_dec_ref(v_inst_3787_);
                    leanh::lean_dec_ref(v_c_3786_);
                    leanh::lean_dec_ref(v_00_u03b1_3785_);
                    leanh::lean_inc(v_a_3800_);
                    leanh::lean_inc_ref(v_a_3799_);
                    leanh::lean_inc(v_a_3798_);
                    leanh::lean_inc_ref(v_a_3797_);
                    leanh::lean_inc(v_a_3796_);
                    leanh::lean_inc_ref(v_a_3795_);
                    leanh::lean_inc(v_a_3794_);
                    leanh::lean_inc_ref(v_a_3793_);
                    leanh::lean_inc(v_a_3792_);
                    v___x_3809_ = leanh::lean_apply_10(
                        v_fallback_3791_,
                        v_a_3792_,
                        v_a_3793_,
                        v_a_3794_,
                        v_a_3795_,
                        v_a_3796_,
                        v_a_3797_,
                        v_a_3798_,
                        v_a_3799_,
                        v_a_3800_,
                        leanh::lean_box(0),
                    );
                    return v___x_3809_;
                } else {
                    v_arg_3810_ = leanh::lean_ctor_get(v___x_3807_, 1);
                    leanh::lean_inc_ref(v_arg_3810_);
                    v___x_3811_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3807_);
                    v___x_3812_ = l_Lean_Expr_isApp(v___x_3811_);
                    if v___x_3812_ == 0 {
                        leanh::lean_dec_ref(v___x_3811_);
                        leanh::lean_dec_ref(v_arg_3810_);
                        leanh::lean_del_object(v___x_3805_);
                        leanh::lean_dec_ref(v_b_3789_);
                        leanh::lean_dec_ref(v_a_3788_);
                        leanh::lean_dec_ref(v_inst_3787_);
                        leanh::lean_dec_ref(v_c_3786_);
                        leanh::lean_dec_ref(v_00_u03b1_3785_);
                        leanh::lean_inc(v_a_3800_);
                        leanh::lean_inc_ref(v_a_3799_);
                        leanh::lean_inc(v_a_3798_);
                        leanh::lean_inc_ref(v_a_3797_);
                        leanh::lean_inc(v_a_3796_);
                        leanh::lean_inc_ref(v_a_3795_);
                        leanh::lean_inc(v_a_3794_);
                        leanh::lean_inc_ref(v_a_3793_);
                        leanh::lean_inc(v_a_3792_);
                        v___x_3813_ = leanh::lean_apply_10(
                            v_fallback_3791_,
                            v_a_3792_,
                            v_a_3793_,
                            v_a_3794_,
                            v_a_3795_,
                            v_a_3796_,
                            v_a_3797_,
                            v_a_3798_,
                            v_a_3799_,
                            v_a_3800_,
                            leanh::lean_box(0),
                        );
                        return v___x_3813_;
                    } else {
                        v___x_3814_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3811_);
                        v___x_3815_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1;
                        v___x_3816_ = l_Lean_Expr_isConstOf(v___x_3814_, v___x_3815_);
                        if v___x_3816_ == 0 {
                            v___x_3817_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3;
                            v___x_3818_ = l_Lean_Expr_isConstOf(v___x_3814_, v___x_3817_);
                            leanh::lean_dec_ref(v___x_3814_);
                            if v___x_3818_ == 0 {
                                leanh::lean_dec_ref(v_arg_3810_);
                                leanh::lean_del_object(v___x_3805_);
                                leanh::lean_dec_ref(v_b_3789_);
                                leanh::lean_dec_ref(v_a_3788_);
                                leanh::lean_dec_ref(v_inst_3787_);
                                leanh::lean_dec_ref(v_c_3786_);
                                leanh::lean_dec_ref(v_00_u03b1_3785_);
                                leanh::lean_inc(v_a_3800_);
                                leanh::lean_inc_ref(v_a_3799_);
                                leanh::lean_inc(v_a_3798_);
                                leanh::lean_inc_ref(v_a_3797_);
                                leanh::lean_inc(v_a_3796_);
                                leanh::lean_inc_ref(v_a_3795_);
                                leanh::lean_inc(v_a_3794_);
                                leanh::lean_inc_ref(v_a_3793_);
                                leanh::lean_inc(v_a_3792_);
                                v___x_3819_ = leanh::lean_apply_10(
                                    v_fallback_3791_,
                                    v_a_3792_,
                                    v_a_3793_,
                                    v_a_3794_,
                                    v_a_3795_,
                                    v_a_3796_,
                                    v_a_3797_,
                                    v_a_3798_,
                                    v_a_3799_,
                                    v_a_3800_,
                                    leanh::lean_box(0),
                                );
                                return v___x_3819_;
                            } else {
                                leanh::lean_dec_ref(v_fallback_3791_);
                                v___x_3820_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__7;
                                v___x_3821_ = l_Lean_Expr_constLevels_x21(v_f_3784_);
                                v___x_3822_ = l_Lean_mkConst(v___x_3820_, v___x_3821_);
                                leanh::lean_inc_ref(v_a_3788_);
                                v___x_3823_ = l_Lean_mkApp6(
                                    v___x_3822_,
                                    v_00_u03b1_3785_,
                                    v_c_3786_,
                                    v_inst_3787_,
                                    v_a_3788_,
                                    v_b_3789_,
                                    v_arg_3810_,
                                );
                                v___x_3824_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                                leanh::lean_ctor_set(v___x_3824_, 0, v_a_3788_);
                                leanh::lean_ctor_set(v___x_3824_, 1, v___x_3823_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_3824_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                    v___x_3816_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_3824_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                        as u32,
                                    v___x_3816_,
                                );
                                if v_isShared_3806_ == 0 {
                                    leanh::lean_ctor_set(v___x_3805_, 0, v___x_3824_);
                                    v___x_3826_ = v___x_3805_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3827_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3827_,
                                        0,
                                        v___x_3824_,
                                    );
                                    v___x_3826_ = v_reuseFailAlloc_3827_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3814_);
                            leanh::lean_dec_ref(v_fallback_3791_);
                            v___x_3828_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__9;
                            v___x_3829_ = l_Lean_Expr_constLevels_x21(v_f_3784_);
                            v___x_3830_ = l_Lean_mkConst(v___x_3828_, v___x_3829_);
                            leanh::lean_inc_ref(v_b_3789_);
                            v___x_3831_ = l_Lean_mkApp6(
                                v___x_3830_,
                                v_00_u03b1_3785_,
                                v_c_3786_,
                                v_inst_3787_,
                                v_a_3788_,
                                v_b_3789_,
                                v_arg_3810_,
                            );
                            v___x_3832_ = 0;
                            v___x_3833_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                            leanh::lean_ctor_set(v___x_3833_, 0, v_b_3789_);
                            leanh::lean_ctor_set(v___x_3833_, 1, v___x_3831_);
                            leanh::lean_ctor_set_uint8(
                                v___x_3833_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v___x_3832_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_3833_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                                v___x_3832_,
                            );
                            if v_isShared_3806_ == 0 {
                                leanh::lean_ctor_set(v___x_3805_, 0, v___x_3833_);
                                v___x_3835_ = v___x_3805_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3836_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3836_, 0, v___x_3833_);
                                v___x_3835_ = v_reuseFailAlloc_3836_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3826_;
            }
            3 => {
                return v___x_3835_;
            }
            4 => {
                if v_isShared_3841_ == 0 {
                    v___x_3843_ = v___x_3840_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3844_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
                    v___x_3843_ = v_reuseFailAlloc_3844_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3843_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_3846_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_3847_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_3848_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_3849_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_3850_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_3851_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_instToMatch_3852_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_fallback_3853_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_3854_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_3855_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_3856_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_3857_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_3858_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_3859_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_3860_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_3861_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_3862_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_3863_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3864_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(
            v_f_3846_,
            v_00_u03b1_3847_,
            v_c_3848_,
            v_inst_3849_,
            v_a_3850_,
            v_b_3851_,
            v_instToMatch_3852_,
            v_fallback_3853_,
            v_a_3854_,
            v_a_3855_,
            v_a_3856_,
            v_a_3857_,
            v_a_3858_,
            v_a_3859_,
            v_a_3860_,
            v_a_3861_,
            v_a_3862_,
        );
    leanh::lean_dec(v_a_3862_);
    leanh::lean_dec_ref(v_a_3861_);
    leanh::lean_dec(v_a_3860_);
    leanh::lean_dec_ref(v_a_3859_);
    leanh::lean_dec(v_a_3858_);
    leanh::lean_dec_ref(v_a_3857_);
    leanh::lean_dec(v_a_3856_);
    leanh::lean_dec_ref(v_a_3855_);
    leanh::lean_dec(v_a_3854_);
    leanh::lean_dec_ref(v_f_3846_);
    return v_res_3864_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(
    mut v_f_3875_: *mut leanh::LeanObject,
    mut v_00_u03b1_3876_: *mut leanh::LeanObject,
    mut v_c_3877_: *mut leanh::LeanObject,
    mut v_inst_3878_: *mut leanh::LeanObject,
    mut v_a_3879_: *mut leanh::LeanObject,
    mut v_b_3880_: *mut leanh::LeanObject,
    mut v_c_x27_3881_: *mut leanh::LeanObject,
    mut v_h_3882_: *mut leanh::LeanObject,
    mut v_inst_x27_3883_: *mut leanh::LeanObject,
    mut v_fallback_3884_: *mut leanh::LeanObject,
    mut v_a_3885_: *mut leanh::LeanObject,
    mut v_a_3886_: *mut leanh::LeanObject,
    mut v_a_3887_: *mut leanh::LeanObject,
    mut v_a_3888_: *mut leanh::LeanObject,
    mut v_a_3889_: *mut leanh::LeanObject,
    mut v_a_3890_: *mut leanh::LeanObject,
    mut v_a_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
    mut v_a_3893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: u8 = 0;
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: u8 = 0;
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: u8 = 0;
    let mut v___x_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: u8 = 0;
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut v_a_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3934_: u8 = 0;
    let mut v___x_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3895_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_3883_, v_a_3891_);
                if leanh::lean_obj_tag(v___x_3895_) == 0 {
                    v_a_3896_ = leanh::lean_ctor_get(v___x_3895_, 0);
                    v_isSharedCheck_3930_ = (!leanh::lean_is_exclusive(v___x_3895_)) as u8;
                    if v_isSharedCheck_3930_ == 0 {
                        v___x_3898_ = v___x_3895_;
                        v_isShared_3899_ = v_isSharedCheck_3930_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3896_);
                        leanh::lean_dec(v___x_3895_);
                        v___x_3898_ = leanh::lean_box(0);
                        v_isShared_3899_ = v_isSharedCheck_3930_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_3884_);
                    leanh::lean_dec_ref(v_h_3882_);
                    leanh::lean_dec_ref(v_c_x27_3881_);
                    leanh::lean_dec_ref(v_b_3880_);
                    leanh::lean_dec_ref(v_a_3879_);
                    leanh::lean_dec_ref(v_inst_3878_);
                    leanh::lean_dec_ref(v_c_3877_);
                    leanh::lean_dec_ref(v_00_u03b1_3876_);
                    v_a_3931_ = leanh::lean_ctor_get(v___x_3895_, 0);
                    v_isSharedCheck_3938_ = (!leanh::lean_is_exclusive(v___x_3895_)) as u8;
                    if v_isSharedCheck_3938_ == 0 {
                        v___x_3933_ = v___x_3895_;
                        v_isShared_3934_ = v_isSharedCheck_3938_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3931_);
                        leanh::lean_dec(v___x_3895_);
                        v___x_3933_ = leanh::lean_box(0);
                        v_isShared_3934_ = v_isSharedCheck_3938_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3900_ = l_Lean_Expr_cleanupAnnotations(v_a_3896_);
                v___x_3901_ = l_Lean_Expr_isApp(v___x_3900_);
                if v___x_3901_ == 0 {
                    leanh::lean_dec_ref(v___x_3900_);
                    leanh::lean_del_object(v___x_3898_);
                    leanh::lean_dec_ref(v_h_3882_);
                    leanh::lean_dec_ref(v_c_x27_3881_);
                    leanh::lean_dec_ref(v_b_3880_);
                    leanh::lean_dec_ref(v_a_3879_);
                    leanh::lean_dec_ref(v_inst_3878_);
                    leanh::lean_dec_ref(v_c_3877_);
                    leanh::lean_dec_ref(v_00_u03b1_3876_);
                    leanh::lean_inc(v_a_3893_);
                    leanh::lean_inc_ref(v_a_3892_);
                    leanh::lean_inc(v_a_3891_);
                    leanh::lean_inc_ref(v_a_3890_);
                    leanh::lean_inc(v_a_3889_);
                    leanh::lean_inc_ref(v_a_3888_);
                    leanh::lean_inc(v_a_3887_);
                    leanh::lean_inc_ref(v_a_3886_);
                    leanh::lean_inc(v_a_3885_);
                    v___x_3902_ = leanh::lean_apply_10(
                        v_fallback_3884_,
                        v_a_3885_,
                        v_a_3886_,
                        v_a_3887_,
                        v_a_3888_,
                        v_a_3889_,
                        v_a_3890_,
                        v_a_3891_,
                        v_a_3892_,
                        v_a_3893_,
                        leanh::lean_box(0),
                    );
                    return v___x_3902_;
                } else {
                    v_arg_3903_ = leanh::lean_ctor_get(v___x_3900_, 1);
                    leanh::lean_inc_ref(v_arg_3903_);
                    v___x_3904_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3900_);
                    v___x_3905_ = l_Lean_Expr_isApp(v___x_3904_);
                    if v___x_3905_ == 0 {
                        leanh::lean_dec_ref(v___x_3904_);
                        leanh::lean_dec_ref(v_arg_3903_);
                        leanh::lean_del_object(v___x_3898_);
                        leanh::lean_dec_ref(v_h_3882_);
                        leanh::lean_dec_ref(v_c_x27_3881_);
                        leanh::lean_dec_ref(v_b_3880_);
                        leanh::lean_dec_ref(v_a_3879_);
                        leanh::lean_dec_ref(v_inst_3878_);
                        leanh::lean_dec_ref(v_c_3877_);
                        leanh::lean_dec_ref(v_00_u03b1_3876_);
                        leanh::lean_inc(v_a_3893_);
                        leanh::lean_inc_ref(v_a_3892_);
                        leanh::lean_inc(v_a_3891_);
                        leanh::lean_inc_ref(v_a_3890_);
                        leanh::lean_inc(v_a_3889_);
                        leanh::lean_inc_ref(v_a_3888_);
                        leanh::lean_inc(v_a_3887_);
                        leanh::lean_inc_ref(v_a_3886_);
                        leanh::lean_inc(v_a_3885_);
                        v___x_3906_ = leanh::lean_apply_10(
                            v_fallback_3884_,
                            v_a_3885_,
                            v_a_3886_,
                            v_a_3887_,
                            v_a_3888_,
                            v_a_3889_,
                            v_a_3890_,
                            v_a_3891_,
                            v_a_3892_,
                            v_a_3893_,
                            leanh::lean_box(0),
                        );
                        return v___x_3906_;
                    } else {
                        v___x_3907_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3904_);
                        v___x_3908_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1;
                        v___x_3909_ = l_Lean_Expr_isConstOf(v___x_3907_, v___x_3908_);
                        if v___x_3909_ == 0 {
                            v___x_3910_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3;
                            v___x_3911_ = l_Lean_Expr_isConstOf(v___x_3907_, v___x_3910_);
                            leanh::lean_dec_ref(v___x_3907_);
                            if v___x_3911_ == 0 {
                                leanh::lean_dec_ref(v_arg_3903_);
                                leanh::lean_del_object(v___x_3898_);
                                leanh::lean_dec_ref(v_h_3882_);
                                leanh::lean_dec_ref(v_c_x27_3881_);
                                leanh::lean_dec_ref(v_b_3880_);
                                leanh::lean_dec_ref(v_a_3879_);
                                leanh::lean_dec_ref(v_inst_3878_);
                                leanh::lean_dec_ref(v_c_3877_);
                                leanh::lean_dec_ref(v_00_u03b1_3876_);
                                leanh::lean_inc(v_a_3893_);
                                leanh::lean_inc_ref(v_a_3892_);
                                leanh::lean_inc(v_a_3891_);
                                leanh::lean_inc_ref(v_a_3890_);
                                leanh::lean_inc(v_a_3889_);
                                leanh::lean_inc_ref(v_a_3888_);
                                leanh::lean_inc(v_a_3887_);
                                leanh::lean_inc_ref(v_a_3886_);
                                leanh::lean_inc(v_a_3885_);
                                v___x_3912_ = leanh::lean_apply_10(
                                    v_fallback_3884_,
                                    v_a_3885_,
                                    v_a_3886_,
                                    v_a_3887_,
                                    v_a_3888_,
                                    v_a_3889_,
                                    v_a_3890_,
                                    v_a_3891_,
                                    v_a_3892_,
                                    v_a_3893_,
                                    leanh::lean_box(0),
                                );
                                return v___x_3912_;
                            } else {
                                leanh::lean_dec_ref(v_fallback_3884_);
                                v___x_3913_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__1;
                                v___x_3914_ = l_Lean_Expr_constLevels_x21(v_f_3875_);
                                v___x_3915_ = l_Lean_mkConst(v___x_3913_, v___x_3914_);
                                leanh::lean_inc_ref(v_a_3879_);
                                v___x_3916_ = l_Lean_mkApp8(
                                    v___x_3915_,
                                    v_00_u03b1_3876_,
                                    v_c_3877_,
                                    v_inst_3878_,
                                    v_a_3879_,
                                    v_b_3880_,
                                    v_c_x27_3881_,
                                    v_h_3882_,
                                    v_arg_3903_,
                                );
                                v___x_3917_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                                leanh::lean_ctor_set(v___x_3917_, 0, v_a_3879_);
                                leanh::lean_ctor_set(v___x_3917_, 1, v___x_3916_);
                                leanh::lean_ctor_set_uint8(
                                    v___x_3917_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                                        as u32,
                                    v___x_3909_,
                                );
                                leanh::lean_ctor_set_uint8(
                                    v___x_3917_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                        as u32,
                                    v___x_3909_,
                                );
                                if v_isShared_3899_ == 0 {
                                    leanh::lean_ctor_set(v___x_3898_, 0, v___x_3917_);
                                    v___x_3919_ = v___x_3898_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3920_ =
                                        leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3920_,
                                        0,
                                        v___x_3917_,
                                    );
                                    v___x_3919_ = v_reuseFailAlloc_3920_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_3907_);
                            leanh::lean_dec_ref(v_fallback_3884_);
                            v___x_3921_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___closed__3;
                            v___x_3922_ = l_Lean_Expr_constLevels_x21(v_f_3875_);
                            v___x_3923_ = l_Lean_mkConst(v___x_3921_, v___x_3922_);
                            leanh::lean_inc_ref(v_b_3880_);
                            v___x_3924_ = l_Lean_mkApp8(
                                v___x_3923_,
                                v_00_u03b1_3876_,
                                v_c_3877_,
                                v_inst_3878_,
                                v_a_3879_,
                                v_b_3880_,
                                v_c_x27_3881_,
                                v_h_3882_,
                                v_arg_3903_,
                            );
                            v___x_3925_ = 0;
                            v___x_3926_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                            leanh::lean_ctor_set(v___x_3926_, 0, v_b_3880_);
                            leanh::lean_ctor_set(v___x_3926_, 1, v___x_3924_);
                            leanh::lean_ctor_set_uint8(
                                v___x_3926_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v___x_3925_,
                            );
                            leanh::lean_ctor_set_uint8(
                                v___x_3926_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                                v___x_3925_,
                            );
                            if v_isShared_3899_ == 0 {
                                leanh::lean_ctor_set(v___x_3898_, 0, v___x_3926_);
                                v___x_3928_ = v___x_3898_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_3929_ =
                                    leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
                                v___x_3928_ = v_reuseFailAlloc_3929_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3919_;
            }
            3 => {
                return v___x_3928_;
            }
            4 => {
                if v_isShared_3934_ == 0 {
                    v___x_3936_ = v___x_3933_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
                    v___x_3936_ = v_reuseFailAlloc_3937_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_3939_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_3940_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_3941_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_3942_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_3943_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_3944_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_c_x27_3945_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_h_3946_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_x27_3947_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_fallback_3948_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_3949_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_3950_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_3951_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_3952_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_3953_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_3954_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_3955_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_3956_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_3957_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_3958_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_res_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3959_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(
            v_f_3939_,
            v_00_u03b1_3940_,
            v_c_3941_,
            v_inst_3942_,
            v_a_3943_,
            v_b_3944_,
            v_c_x27_3945_,
            v_h_3946_,
            v_inst_x27_3947_,
            v_fallback_3948_,
            v_a_3949_,
            v_a_3950_,
            v_a_3951_,
            v_a_3952_,
            v_a_3953_,
            v_a_3954_,
            v_a_3955_,
            v_a_3956_,
            v_a_3957_,
        );
    leanh::lean_dec(v_a_3957_);
    leanh::lean_dec_ref(v_a_3956_);
    leanh::lean_dec(v_a_3955_);
    leanh::lean_dec_ref(v_a_3954_);
    leanh::lean_dec(v_a_3953_);
    leanh::lean_dec_ref(v_a_3952_);
    leanh::lean_dec(v_a_3951_);
    leanh::lean_dec_ref(v_a_3950_);
    leanh::lean_dec(v_a_3949_);
    leanh::lean_dec_ref(v_f_3939_);
    return v_res_3959_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(
    mut v_f_3960_: *mut leanh::LeanObject,
    mut v_00_u03b1_3961_: *mut leanh::LeanObject,
    mut v_c_3962_: *mut leanh::LeanObject,
    mut v_inst_3963_: *mut leanh::LeanObject,
    mut v_a_3964_: *mut leanh::LeanObject,
    mut v_b_3965_: *mut leanh::LeanObject,
    mut v_fallback_3966_: *mut leanh::LeanObject,
    mut v_a_3967_: *mut leanh::LeanObject,
    mut v_a_3968_: *mut leanh::LeanObject,
    mut v_a_3969_: *mut leanh::LeanObject,
    mut v_a_3970_: *mut leanh::LeanObject,
    mut v_a_3971_: *mut leanh::LeanObject,
    mut v_a_3972_: *mut leanh::LeanObject,
    mut v_a_3973_: *mut leanh::LeanObject,
    mut v_a_3974_: *mut leanh::LeanObject,
    mut v_a_3975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3979_: u8 = 0;
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3983_: u8 = 0;
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3986_: u8 = 0;
    let mut v___x_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3991_: u8 = 0;
    let mut v_unused_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3993_: u8 = 0;
    let mut v_contextDependent_3994_: u8 = 0;
    let mut v_e_x27_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_3996_: u8 = 0;
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4000_: u8 = 0;
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4003_: u8 = 0;
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4008_: u8 = 0;
    let mut v_unused_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4010_: u8 = 0;
    let mut v_contextDependent_4011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_3975_);
                leanh::lean_inc_ref(v_a_3974_);
                leanh::lean_inc(v_a_3973_);
                leanh::lean_inc_ref(v_a_3972_);
                leanh::lean_inc(v_a_3971_);
                leanh::lean_inc_ref(v_a_3970_);
                leanh::lean_inc(v_a_3969_);
                leanh::lean_inc_ref(v_a_3968_);
                leanh::lean_inc(v_a_3967_);
                leanh::lean_inc_ref(v_inst_3963_);
                v___x_3977_ = lean_sym_simp(
                    v_inst_3963_,
                    v_a_3967_,
                    v_a_3968_,
                    v_a_3969_,
                    v_a_3970_,
                    v_a_3971_,
                    v_a_3972_,
                    v_a_3973_,
                    v_a_3974_,
                    v_a_3975_,
                );
                if leanh::lean_obj_tag(v___x_3977_) == 0 {
                    v_a_3978_ = leanh::lean_ctor_get(v___x_3977_, 0);
                    leanh::lean_inc(v_a_3978_);
                    leanh::lean_dec_ref_known(v___x_3977_, 1);
                    if leanh::lean_obj_tag(v_a_3978_) == 0 {
                        v_contextDependent_3979_ =
                            leanh::lean_ctor_get_uint8(v_a_3978_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_3978_, 0);
                        leanh::lean_inc_ref(v_inst_3963_);
                        v___x_3980_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_3960_, v_00_u03b1_3961_, v_c_3962_, v_inst_3963_, v_a_3964_, v_b_3965_, v_inst_3963_, v_fallback_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
                        if leanh::lean_obj_tag(v___x_3980_) == 0 {
                            v_a_3981_ = leanh::lean_ctor_get(v___x_3980_, 0);
                            leanh::lean_inc(v_a_3981_);
                            if v_contextDependent_3979_ == 0 {
                                leanh::lean_dec(v_a_3981_);
                                return v___x_3980_;
                            } else {
                                if leanh::lean_obj_tag(v_a_3981_) == 0 {
                                    v_contextDependent_3993_ =
                                        leanh::lean_ctor_get_uint8(v_a_3981_, 1 as u32);
                                    v___y_3983_ = v_contextDependent_3993_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_contextDependent_3994_ = leanh::lean_ctor_get_uint8(
                                        v_a_3981_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_3983_ = v_contextDependent_3994_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_3980_;
                        }
                    } else {
                        v_e_x27_3995_ = leanh::lean_ctor_get(v_a_3978_, 0);
                        leanh::lean_inc_ref(v_e_x27_3995_);
                        v_contextDependent_3996_ = leanh::lean_ctor_get_uint8(
                            v_a_3978_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        leanh::lean_dec_ref_known(v_a_3978_, 2);
                        v___x_3997_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable(v_f_3960_, v_00_u03b1_3961_, v_c_3962_, v_inst_3963_, v_a_3964_, v_b_3965_, v_e_x27_3995_, v_fallback_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
                        if leanh::lean_obj_tag(v___x_3997_) == 0 {
                            v_a_3998_ = leanh::lean_ctor_get(v___x_3997_, 0);
                            leanh::lean_inc(v_a_3998_);
                            if v_contextDependent_3996_ == 0 {
                                leanh::lean_dec(v_a_3998_);
                                return v___x_3997_;
                            } else {
                                if leanh::lean_obj_tag(v_a_3998_) == 0 {
                                    v_contextDependent_4010_ =
                                        leanh::lean_ctor_get_uint8(v_a_3998_, 1 as u32);
                                    v___y_4000_ = v_contextDependent_4010_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_contextDependent_4011_ = leanh::lean_ctor_get_uint8(
                                        v_a_3998_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_4000_ = v_contextDependent_4011_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_3997_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_3966_);
                    leanh::lean_dec_ref(v_b_3965_);
                    leanh::lean_dec_ref(v_a_3964_);
                    leanh::lean_dec_ref(v_inst_3963_);
                    leanh::lean_dec_ref(v_c_3962_);
                    leanh::lean_dec_ref(v_00_u03b1_3961_);
                    return v___x_3977_;
                }
            }
            1 => {
                if v___y_3983_ == 0 {
                    v_isSharedCheck_3991_ = (!leanh::lean_is_exclusive(v___x_3980_)) as u8;
                    if v_isSharedCheck_3991_ == 0 {
                        v_unused_3992_ = leanh::lean_ctor_get(v___x_3980_, 0);
                        leanh::lean_dec(v_unused_3992_);
                        v___x_3985_ = v___x_3980_;
                        v_isShared_3986_ = v_isSharedCheck_3991_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3980_);
                        v___x_3985_ = leanh::lean_box(0);
                        v_isShared_3986_ = v_isSharedCheck_3991_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3981_);
                    return v___x_3980_;
                }
            }
            2 => {
                v___x_3987_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3981_);
                if v_isShared_3986_ == 0 {
                    leanh::lean_ctor_set(v___x_3985_, 0, v___x_3987_);
                    v___x_3989_ = v___x_3985_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
                    v___x_3989_ = v_reuseFailAlloc_3990_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3989_;
            }
            4 => {
                if v___y_4000_ == 0 {
                    v_isSharedCheck_4008_ = (!leanh::lean_is_exclusive(v___x_3997_)) as u8;
                    if v_isSharedCheck_4008_ == 0 {
                        v_unused_4009_ = leanh::lean_ctor_get(v___x_3997_, 0);
                        leanh::lean_dec(v_unused_4009_);
                        v___x_4002_ = v___x_3997_;
                        v_isShared_4003_ = v_isSharedCheck_4008_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3997_);
                        v___x_4002_ = leanh::lean_box(0);
                        v_isShared_4003_ = v_isSharedCheck_4008_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3998_);
                    return v___x_3997_;
                }
            }
            5 => {
                v___x_4004_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3998_);
                if v_isShared_4003_ == 0 {
                    leanh::lean_ctor_set(v___x_4002_, 0, v___x_4004_);
                    v___x_4006_ = v___x_4002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4007_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4004_);
                    v___x_4006_ = v_reuseFailAlloc_4007_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_4012_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_4013_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_4014_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_4015_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_4016_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4017_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_fallback_4018_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_a_4019_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_4020_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_4021_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_4022_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_4023_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_4024_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_4025_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_4026_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_4027_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_4028_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4029_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(
            v_f_4012_,
            v_00_u03b1_4013_,
            v_c_4014_,
            v_inst_4015_,
            v_a_4016_,
            v_b_4017_,
            v_fallback_4018_,
            v_a_4019_,
            v_a_4020_,
            v_a_4021_,
            v_a_4022_,
            v_a_4023_,
            v_a_4024_,
            v_a_4025_,
            v_a_4026_,
            v_a_4027_,
        );
    leanh::lean_dec(v_a_4027_);
    leanh::lean_dec_ref(v_a_4026_);
    leanh::lean_dec(v_a_4025_);
    leanh::lean_dec_ref(v_a_4024_);
    leanh::lean_dec(v_a_4023_);
    leanh::lean_dec_ref(v_a_4022_);
    leanh::lean_dec(v_a_4021_);
    leanh::lean_dec_ref(v_a_4020_);
    leanh::lean_dec(v_a_4019_);
    leanh::lean_dec_ref(v_f_4012_);
    return v_res_4029_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(
    mut v_f_4030_: *mut leanh::LeanObject,
    mut v_00_u03b1_4031_: *mut leanh::LeanObject,
    mut v_c_4032_: *mut leanh::LeanObject,
    mut v_inst_4033_: *mut leanh::LeanObject,
    mut v_a_4034_: *mut leanh::LeanObject,
    mut v_b_4035_: *mut leanh::LeanObject,
    mut v_c_x27_4036_: *mut leanh::LeanObject,
    mut v_h_4037_: *mut leanh::LeanObject,
    mut v_inst_x27_4038_: *mut leanh::LeanObject,
    mut v_fallback_4039_: *mut leanh::LeanObject,
    mut v_a_4040_: *mut leanh::LeanObject,
    mut v_a_4041_: *mut leanh::LeanObject,
    mut v_a_4042_: *mut leanh::LeanObject,
    mut v_a_4043_: *mut leanh::LeanObject,
    mut v_a_4044_: *mut leanh::LeanObject,
    mut v_a_4045_: *mut leanh::LeanObject,
    mut v_a_4046_: *mut leanh::LeanObject,
    mut v_a_4047_: *mut leanh::LeanObject,
    mut v_a_4048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4052_: u8 = 0;
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4056_: u8 = 0;
    let mut v___x_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4059_: u8 = 0;
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_unused_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4066_: u8 = 0;
    let mut v_contextDependent_4067_: u8 = 0;
    let mut v_e_x27_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4069_: u8 = 0;
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4073_: u8 = 0;
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4076_: u8 = 0;
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_unused_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4083_: u8 = 0;
    let mut v_contextDependent_4084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_4048_);
                leanh::lean_inc_ref(v_a_4047_);
                leanh::lean_inc(v_a_4046_);
                leanh::lean_inc_ref(v_a_4045_);
                leanh::lean_inc(v_a_4044_);
                leanh::lean_inc_ref(v_a_4043_);
                leanh::lean_inc(v_a_4042_);
                leanh::lean_inc_ref(v_a_4041_);
                leanh::lean_inc(v_a_4040_);
                leanh::lean_inc_ref(v_inst_x27_4038_);
                v___x_4050_ = lean_sym_simp(
                    v_inst_x27_4038_,
                    v_a_4040_,
                    v_a_4041_,
                    v_a_4042_,
                    v_a_4043_,
                    v_a_4044_,
                    v_a_4045_,
                    v_a_4046_,
                    v_a_4047_,
                    v_a_4048_,
                );
                if leanh::lean_obj_tag(v___x_4050_) == 0 {
                    v_a_4051_ = leanh::lean_ctor_get(v___x_4050_, 0);
                    leanh::lean_inc(v_a_4051_);
                    leanh::lean_dec_ref_known(v___x_4050_, 1);
                    if leanh::lean_obj_tag(v_a_4051_) == 0 {
                        v_contextDependent_4052_ =
                            leanh::lean_ctor_get_uint8(v_a_4051_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_4051_, 0);
                        v___x_4053_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_4030_, v_00_u03b1_4031_, v_c_4032_, v_inst_4033_, v_a_4034_, v_b_4035_, v_c_x27_4036_, v_h_4037_, v_inst_x27_4038_, v_fallback_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
                        if leanh::lean_obj_tag(v___x_4053_) == 0 {
                            v_a_4054_ = leanh::lean_ctor_get(v___x_4053_, 0);
                            leanh::lean_inc(v_a_4054_);
                            if v_contextDependent_4052_ == 0 {
                                leanh::lean_dec(v_a_4054_);
                                return v___x_4053_;
                            } else {
                                if leanh::lean_obj_tag(v_a_4054_) == 0 {
                                    v_contextDependent_4066_ =
                                        leanh::lean_ctor_get_uint8(v_a_4054_, 1 as u32);
                                    v___y_4056_ = v_contextDependent_4066_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_contextDependent_4067_ = leanh::lean_ctor_get_uint8(
                                        v_a_4054_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_4056_ = v_contextDependent_4067_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_4053_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_x27_4038_);
                        v_e_x27_4068_ = leanh::lean_ctor_get(v_a_4051_, 0);
                        leanh::lean_inc_ref(v_e_x27_4068_);
                        v_contextDependent_4069_ = leanh::lean_ctor_get_uint8(
                            v_a_4051_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        leanh::lean_dec_ref_known(v_a_4051_, 2);
                        v___x_4070_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidableCongr(v_f_4030_, v_00_u03b1_4031_, v_c_4032_, v_inst_4033_, v_a_4034_, v_b_4035_, v_c_x27_4036_, v_h_4037_, v_e_x27_4068_, v_fallback_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
                        if leanh::lean_obj_tag(v___x_4070_) == 0 {
                            v_a_4071_ = leanh::lean_ctor_get(v___x_4070_, 0);
                            leanh::lean_inc(v_a_4071_);
                            if v_contextDependent_4069_ == 0 {
                                leanh::lean_dec(v_a_4071_);
                                return v___x_4070_;
                            } else {
                                if leanh::lean_obj_tag(v_a_4071_) == 0 {
                                    v_contextDependent_4083_ =
                                        leanh::lean_ctor_get_uint8(v_a_4071_, 1 as u32);
                                    v___y_4073_ = v_contextDependent_4083_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_contextDependent_4084_ = leanh::lean_ctor_get_uint8(
                                        v_a_4071_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_4073_ = v_contextDependent_4084_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_4070_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_4039_);
                    leanh::lean_dec_ref(v_inst_x27_4038_);
                    leanh::lean_dec_ref(v_h_4037_);
                    leanh::lean_dec_ref(v_c_x27_4036_);
                    leanh::lean_dec_ref(v_b_4035_);
                    leanh::lean_dec_ref(v_a_4034_);
                    leanh::lean_dec_ref(v_inst_4033_);
                    leanh::lean_dec_ref(v_c_4032_);
                    leanh::lean_dec_ref(v_00_u03b1_4031_);
                    return v___x_4050_;
                }
            }
            1 => {
                if v___y_4056_ == 0 {
                    v_isSharedCheck_4064_ = (!leanh::lean_is_exclusive(v___x_4053_)) as u8;
                    if v_isSharedCheck_4064_ == 0 {
                        v_unused_4065_ = leanh::lean_ctor_get(v___x_4053_, 0);
                        leanh::lean_dec(v_unused_4065_);
                        v___x_4058_ = v___x_4053_;
                        v_isShared_4059_ = v_isSharedCheck_4064_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4053_);
                        v___x_4058_ = leanh::lean_box(0);
                        v_isShared_4059_ = v_isSharedCheck_4064_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4054_);
                    return v___x_4053_;
                }
            }
            2 => {
                v___x_4060_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4054_);
                if v_isShared_4059_ == 0 {
                    leanh::lean_ctor_set(v___x_4058_, 0, v___x_4060_);
                    v___x_4062_ = v___x_4058_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4062_;
            }
            4 => {
                if v___y_4073_ == 0 {
                    v_isSharedCheck_4081_ = (!leanh::lean_is_exclusive(v___x_4070_)) as u8;
                    if v_isSharedCheck_4081_ == 0 {
                        v_unused_4082_ = leanh::lean_ctor_get(v___x_4070_, 0);
                        leanh::lean_dec(v_unused_4082_);
                        v___x_4075_ = v___x_4070_;
                        v_isShared_4076_ = v_isSharedCheck_4081_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4070_);
                        v___x_4075_ = leanh::lean_box(0);
                        v_isShared_4076_ = v_isSharedCheck_4081_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4071_);
                    return v___x_4070_;
                }
            }
            5 => {
                v___x_4077_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4071_);
                if v_isShared_4076_ == 0 {
                    leanh::lean_ctor_set(v___x_4075_, 0, v___x_4077_);
                    v___x_4079_ = v___x_4075_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4080_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4077_);
                    v___x_4079_ = v_reuseFailAlloc_4080_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4079_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_4085_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_4086_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_4087_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_4088_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_4089_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4090_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_c_x27_4091_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_h_4092_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_x27_4093_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_fallback_4094_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_4095_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_4096_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_4097_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_4098_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_4099_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_4100_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_4101_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_4102_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_4103_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_4104_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_res_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4105_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr(v_f_4085_, v_00_u03b1_4086_, v_c_4087_, v_inst_4088_, v_a_4089_, v_b_4090_, v_c_x27_4091_, v_h_4092_, v_inst_x27_4093_, v_fallback_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_);
    leanh::lean_dec(v_a_4103_);
    leanh::lean_dec_ref(v_a_4102_);
    leanh::lean_dec(v_a_4101_);
    leanh::lean_dec_ref(v_a_4100_);
    leanh::lean_dec(v_a_4099_);
    leanh::lean_dec_ref(v_a_4098_);
    leanh::lean_dec(v_a_4097_);
    leanh::lean_dec_ref(v_a_4096_);
    leanh::lean_dec(v_a_4095_);
    leanh::lean_dec_ref(v_f_4085_);
    return v_res_4105_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(
    mut v___x_4106_: *mut leanh::LeanObject,
    mut v___y_4107_: *mut leanh::LeanObject,
    mut v___y_4108_: *mut leanh::LeanObject,
    mut v___y_4109_: *mut leanh::LeanObject,
    mut v___y_4110_: *mut leanh::LeanObject,
    mut v___y_4111_: *mut leanh::LeanObject,
    mut v___y_4112_: *mut leanh::LeanObject,
    mut v___y_4113_: *mut leanh::LeanObject,
    mut v___y_4114_: *mut leanh::LeanObject,
    mut v___y_4115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4117_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4117_, 0, v___x_4106_);
    return v___x_4117_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed(
    mut v___x_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
    mut v___y_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
    mut v___y_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
    mut v___y_4127_: *mut leanh::LeanObject,
    mut v___y_4128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4129_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0(
            v___x_4118_,
            v___y_4119_,
            v___y_4120_,
            v___y_4121_,
            v___y_4122_,
            v___y_4123_,
            v___y_4124_,
            v___y_4125_,
            v___y_4126_,
            v___y_4127_,
        );
    leanh::lean_dec(v___y_4127_);
    leanh::lean_dec_ref(v___y_4126_);
    leanh::lean_dec(v___y_4125_);
    leanh::lean_dec_ref(v___y_4124_);
    leanh::lean_dec(v___y_4123_);
    leanh::lean_dec_ref(v___y_4122_);
    leanh::lean_dec(v___y_4121_);
    leanh::lean_dec_ref(v___y_4120_);
    leanh::lean_dec(v___y_4119_);
    return v_res_4129_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(
    mut v_f_4130_: *mut leanh::LeanObject,
    mut v_a_4131_: *mut leanh::LeanObject,
    mut v___y_4132_: *mut leanh::LeanObject,
    mut v___y_4133_: *mut leanh::LeanObject,
    mut v___y_4134_: *mut leanh::LeanObject,
    mut v___y_4135_: *mut leanh::LeanObject,
    mut v___y_4136_: *mut leanh::LeanObject,
    mut v___y_4137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_4144_: u8 = 0;
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4150_: u8 = 0;
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4154_: u8 = 0;
    let mut v_a_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4158_: u8 = 0;
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4162_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4143_ = lean_st_ref_get(v___y_4133_);
                v_debug_4144_ = leanh::lean_ctor_get_uint8(
                    v___x_4143_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                leanh::lean_dec(v___x_4143_);
                if v_debug_4144_ == 0 {
                    v___y_4140_ = v___y_4133_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_f_4130_);
                    v___x_4145_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_4130_,
                        v___y_4132_,
                        v___y_4133_,
                        v___y_4134_,
                        v___y_4135_,
                        v___y_4136_,
                        v___y_4137_,
                    );
                    if leanh::lean_obj_tag(v___x_4145_) == 0 {
                        leanh::lean_dec_ref_known(v___x_4145_, 1);
                        leanh::lean_inc_ref(v_a_4131_);
                        v___x_4146_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_4131_,
                            v___y_4132_,
                            v___y_4133_,
                            v___y_4134_,
                            v___y_4135_,
                            v___y_4136_,
                            v___y_4137_,
                        );
                        if leanh::lean_obj_tag(v___x_4146_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4146_, 1);
                            v___y_4140_ = v___y_4133_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_a_4131_);
                            leanh::lean_dec_ref(v_f_4130_);
                            v_a_4147_ = leanh::lean_ctor_get(v___x_4146_, 0);
                            v_isSharedCheck_4154_ =
                                (!leanh::lean_is_exclusive(v___x_4146_)) as u8;
                            if v_isSharedCheck_4154_ == 0 {
                                v___x_4149_ = v___x_4146_;
                                v_isShared_4150_ = v_isSharedCheck_4154_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4147_);
                                leanh::lean_dec(v___x_4146_);
                                v___x_4149_ = leanh::lean_box(0);
                                v_isShared_4150_ = v_isSharedCheck_4154_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_4131_);
                        leanh::lean_dec_ref(v_f_4130_);
                        v_a_4155_ = leanh::lean_ctor_get(v___x_4145_, 0);
                        v_isSharedCheck_4162_ =
                            (!leanh::lean_is_exclusive(v___x_4145_)) as u8;
                        if v_isSharedCheck_4162_ == 0 {
                            v___x_4157_ = v___x_4145_;
                            v_isShared_4158_ = v_isSharedCheck_4162_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4155_);
                            leanh::lean_dec(v___x_4145_);
                            v___x_4157_ = leanh::lean_box(0);
                            v_isShared_4158_ = v_isSharedCheck_4162_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4141_ = l_Lean_Expr_app___override(v_f_4130_, v_a_4131_);
                v___x_4142_ =
                    l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_4141_, v___y_4140_);
                return v___x_4142_;
            }
            2 => {
                if v_isShared_4150_ == 0 {
                    v___x_4152_ = v___x_4149_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4153_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
                    v___x_4152_ = v_reuseFailAlloc_4153_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4152_;
            }
            4 => {
                if v_isShared_4158_ == 0 {
                    v___x_4160_ = v___x_4157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4161_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
                    v___x_4160_ = v_reuseFailAlloc_4161_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4160_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg___boxed(
    mut v_f_4163_: *mut leanh::LeanObject,
    mut v_a_4164_: *mut leanh::LeanObject,
    mut v___y_4165_: *mut leanh::LeanObject,
    mut v___y_4166_: *mut leanh::LeanObject,
    mut v___y_4167_: *mut leanh::LeanObject,
    mut v___y_4168_: *mut leanh::LeanObject,
    mut v___y_4169_: *mut leanh::LeanObject,
    mut v___y_4170_: *mut leanh::LeanObject,
    mut v___y_4171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4172_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_4163_, v_a_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
    leanh::lean_dec(v___y_4170_);
    leanh::lean_dec_ref(v___y_4169_);
    leanh::lean_dec(v___y_4168_);
    leanh::lean_dec_ref(v___y_4167_);
    leanh::lean_dec(v___y_4166_);
    leanh::lean_dec_ref(v___y_4165_);
    return v_res_4172_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(
    mut v_f_4173_: *mut leanh::LeanObject,
    mut v_a_u2081_4174_: *mut leanh::LeanObject,
    mut v_a_u2082_4175_: *mut leanh::LeanObject,
    mut v___y_4176_: *mut leanh::LeanObject,
    mut v___y_4177_: *mut leanh::LeanObject,
    mut v___y_4178_: *mut leanh::LeanObject,
    mut v___y_4179_: *mut leanh::LeanObject,
    mut v___y_4180_: *mut leanh::LeanObject,
    mut v___y_4181_: *mut leanh::LeanObject,
    mut v___y_4182_: *mut leanh::LeanObject,
    mut v___y_4183_: *mut leanh::LeanObject,
    mut v___y_4184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4186_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_4173_, v_a_u2081_4174_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
    if leanh::lean_obj_tag(v___x_4186_) == 0 {
        let mut v_a_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4187_ = leanh::lean_ctor_get(v___x_4186_, 0);
        leanh::lean_inc(v_a_4187_);
        leanh::lean_dec_ref_known(v___x_4186_, 1);
        v___x_4188_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_4187_, v_a_u2082_4175_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
        return v___x_4188_;
    } else {
        leanh::lean_dec_ref(v_a_u2082_4175_);
        return v___x_4186_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1___boxed(
    mut v_f_4189_: *mut leanh::LeanObject,
    mut v_a_u2081_4190_: *mut leanh::LeanObject,
    mut v_a_u2082_4191_: *mut leanh::LeanObject,
    mut v___y_4192_: *mut leanh::LeanObject,
    mut v___y_4193_: *mut leanh::LeanObject,
    mut v___y_4194_: *mut leanh::LeanObject,
    mut v___y_4195_: *mut leanh::LeanObject,
    mut v___y_4196_: *mut leanh::LeanObject,
    mut v___y_4197_: *mut leanh::LeanObject,
    mut v___y_4198_: *mut leanh::LeanObject,
    mut v___y_4199_: *mut leanh::LeanObject,
    mut v___y_4200_: *mut leanh::LeanObject,
    mut v___y_4201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4202_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_4189_, v_a_u2081_4190_, v_a_u2082_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
    leanh::lean_dec(v___y_4200_);
    leanh::lean_dec_ref(v___y_4199_);
    leanh::lean_dec(v___y_4198_);
    leanh::lean_dec_ref(v___y_4197_);
    leanh::lean_dec(v___y_4196_);
    leanh::lean_dec_ref(v___y_4195_);
    leanh::lean_dec(v___y_4194_);
    leanh::lean_dec_ref(v___y_4193_);
    leanh::lean_dec(v___y_4192_);
    return v_res_4202_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(
    mut v_f_4203_: *mut leanh::LeanObject,
    mut v_a_u2081_4204_: *mut leanh::LeanObject,
    mut v_a_u2082_4205_: *mut leanh::LeanObject,
    mut v_a_u2083_4206_: *mut leanh::LeanObject,
    mut v___y_4207_: *mut leanh::LeanObject,
    mut v___y_4208_: *mut leanh::LeanObject,
    mut v___y_4209_: *mut leanh::LeanObject,
    mut v___y_4210_: *mut leanh::LeanObject,
    mut v___y_4211_: *mut leanh::LeanObject,
    mut v___y_4212_: *mut leanh::LeanObject,
    mut v___y_4213_: *mut leanh::LeanObject,
    mut v___y_4214_: *mut leanh::LeanObject,
    mut v___y_4215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4217_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_f_4203_, v_a_u2081_4204_, v_a_u2082_4205_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
    if leanh::lean_obj_tag(v___x_4217_) == 0 {
        let mut v_a_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4218_ = leanh::lean_ctor_get(v___x_4217_, 0);
        leanh::lean_inc(v_a_4218_);
        leanh::lean_dec_ref_known(v___x_4217_, 1);
        v___x_4219_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_4218_, v_a_u2083_4206_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_, v___y_4215_);
        return v___x_4219_;
    } else {
        leanh::lean_dec_ref(v_a_u2083_4206_);
        return v___x_4217_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0___boxed(
    mut v_f_4220_: *mut leanh::LeanObject,
    mut v_a_u2081_4221_: *mut leanh::LeanObject,
    mut v_a_u2082_4222_: *mut leanh::LeanObject,
    mut v_a_u2083_4223_: *mut leanh::LeanObject,
    mut v___y_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
    mut v___y_4232_: *mut leanh::LeanObject,
    mut v___y_4233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4234_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_4220_, v_a_u2081_4221_, v_a_u2082_4222_, v_a_u2083_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
    leanh::lean_dec(v___y_4232_);
    leanh::lean_dec_ref(v___y_4231_);
    leanh::lean_dec(v___y_4230_);
    leanh::lean_dec_ref(v___y_4229_);
    leanh::lean_dec(v___y_4228_);
    leanh::lean_dec_ref(v___y_4227_);
    leanh::lean_dec(v___y_4226_);
    leanh::lean_dec_ref(v___y_4225_);
    leanh::lean_dec(v___y_4224_);
    return v_res_4234_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(
    mut v_f_4235_: *mut leanh::LeanObject,
    mut v_a_u2081_4236_: *mut leanh::LeanObject,
    mut v_a_u2082_4237_: *mut leanh::LeanObject,
    mut v_a_u2083_4238_: *mut leanh::LeanObject,
    mut v_a_u2084_4239_: *mut leanh::LeanObject,
    mut v___y_4240_: *mut leanh::LeanObject,
    mut v___y_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
    mut v___y_4245_: *mut leanh::LeanObject,
    mut v___y_4246_: *mut leanh::LeanObject,
    mut v___y_4247_: *mut leanh::LeanObject,
    mut v___y_4248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4250_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0(v_f_4235_, v_a_u2081_4236_, v_a_u2082_4237_, v_a_u2083_4238_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
    if leanh::lean_obj_tag(v___x_4250_) == 0 {
        let mut v_a_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4251_ = leanh::lean_ctor_get(v___x_4250_, 0);
        leanh::lean_inc(v_a_4251_);
        leanh::lean_dec_ref_known(v___x_4250_, 1);
        v___x_4252_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_a_4251_, v_a_u2084_4239_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
        return v___x_4252_;
    } else {
        leanh::lean_dec_ref(v_a_u2084_4239_);
        return v___x_4250_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0___boxed(
    mut v_f_4253_: *mut leanh::LeanObject,
    mut v_a_u2081_4254_: *mut leanh::LeanObject,
    mut v_a_u2082_4255_: *mut leanh::LeanObject,
    mut v_a_u2083_4256_: *mut leanh::LeanObject,
    mut v_a_u2084_4257_: *mut leanh::LeanObject,
    mut v___y_4258_: *mut leanh::LeanObject,
    mut v___y_4259_: *mut leanh::LeanObject,
    mut v___y_4260_: *mut leanh::LeanObject,
    mut v___y_4261_: *mut leanh::LeanObject,
    mut v___y_4262_: *mut leanh::LeanObject,
    mut v___y_4263_: *mut leanh::LeanObject,
    mut v___y_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
    mut v___y_4266_: *mut leanh::LeanObject,
    mut v___y_4267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4268_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v_f_4253_, v_a_u2081_4254_, v_a_u2082_4255_, v_a_u2083_4256_, v_a_u2084_4257_, v___y_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_, v___y_4266_);
    leanh::lean_dec(v___y_4266_);
    leanh::lean_dec_ref(v___y_4265_);
    leanh::lean_dec(v___y_4264_);
    leanh::lean_dec_ref(v___y_4263_);
    leanh::lean_dec(v___y_4262_);
    leanh::lean_dec_ref(v___y_4261_);
    leanh::lean_dec(v___y_4260_);
    leanh::lean_dec_ref(v___y_4259_);
    leanh::lean_dec(v___y_4258_);
    return v_res_4268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(
    mut v___x_4274_: *mut leanh::LeanObject,
    mut v_e_x27_4275_: *mut leanh::LeanObject,
    mut v___x_4276_: *mut leanh::LeanObject,
    mut v_arg_4277_: *mut leanh::LeanObject,
    mut v_arg_4278_: *mut leanh::LeanObject,
    mut v_e_4279_: *mut leanh::LeanObject,
    mut v_proof_4280_: *mut leanh::LeanObject,
    mut v___x_4281_: u8,
    mut v_contextDependent_4282_: u8,
    mut v___y_4283_: *mut leanh::LeanObject,
    mut v___y_4284_: *mut leanh::LeanObject,
    mut v___y_4285_: *mut leanh::LeanObject,
    mut v___y_4286_: *mut leanh::LeanObject,
    mut v___y_4287_: *mut leanh::LeanObject,
    mut v___y_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
    mut v___y_4290_: *mut leanh::LeanObject,
    mut v___y_4291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4297_: u8 = 0;
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut v_a_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4309_: u8 = 0;
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v___x_4276_);
                leanh::lean_inc_ref(v_e_x27_4275_);
                v___x_4293_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_4274_, v_e_x27_4275_, v___x_4276_, v_arg_4277_, v_arg_4278_, v___y_4283_, v___y_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
                if leanh::lean_obj_tag(v___x_4293_) == 0 {
                    v_a_4294_ = leanh::lean_ctor_get(v___x_4293_, 0);
                    v_isSharedCheck_4305_ = (!leanh::lean_is_exclusive(v___x_4293_)) as u8;
                    if v_isSharedCheck_4305_ == 0 {
                        v___x_4296_ = v___x_4293_;
                        v_isShared_4297_ = v_isSharedCheck_4305_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4294_);
                        leanh::lean_dec(v___x_4293_);
                        v___x_4296_ = leanh::lean_box(0);
                        v_isShared_4297_ = v_isSharedCheck_4305_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_proof_4280_);
                    leanh::lean_dec_ref(v_e_4279_);
                    leanh::lean_dec_ref(v___x_4276_);
                    leanh::lean_dec_ref(v_e_x27_4275_);
                    v_a_4306_ = leanh::lean_ctor_get(v___x_4293_, 0);
                    v_isSharedCheck_4313_ = (!leanh::lean_is_exclusive(v___x_4293_)) as u8;
                    if v_isSharedCheck_4313_ == 0 {
                        v___x_4308_ = v___x_4293_;
                        v_isShared_4309_ = v_isSharedCheck_4313_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4306_);
                        leanh::lean_dec(v___x_4293_);
                        v___x_4308_ = leanh::lean_box(0);
                        v_isShared_4309_ = v_isSharedCheck_4313_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4298_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___closed__1;
                v___x_4299_ = l_Lean_Expr_replaceFn(v_e_4279_, v___x_4298_);
                v___x_4300_ = l_Lean_mkApp3(v___x_4299_, v_e_x27_4275_, v___x_4276_, v_proof_4280_);
                v___x_4301_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_4301_, 0, v_a_4294_);
                leanh::lean_ctor_set(v___x_4301_, 1, v___x_4300_);
                leanh::lean_ctor_set_uint8(
                    v___x_4301_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4281_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4301_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_4282_,
                );
                if v_isShared_4297_ == 0 {
                    leanh::lean_ctor_set(v___x_4296_, 0, v___x_4301_);
                    v___x_4303_ = v___x_4296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4304_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4301_);
                    v___x_4303_ = v_reuseFailAlloc_4304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4303_;
            }
            3 => {
                if v_isShared_4309_ == 0 {
                    v___x_4311_ = v___x_4308_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4312_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_a_4306_);
                    v___x_4311_ = v_reuseFailAlloc_4312_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4314_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_e_x27_4315_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_4316_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_arg_4317_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_arg_4318_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_e_4319_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_proof_4320_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_4321_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_contextDependent_4322_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4323_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4324_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4325_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4326_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4327_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4328_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4329_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4330_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4331_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_4332_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___x_18465__boxed_4333_: u8 = 0;
    let mut v_contextDependent_18466__boxed_4334_: u8 = 0;
    let mut v_res_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18465__boxed_4333_ = (leanh::lean_unbox(v___x_4321_) as u8);
    v_contextDependent_18466__boxed_4334_ =
        (leanh::lean_unbox(v_contextDependent_4322_) as u8);
    v_res_4335_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1(
            v___x_4314_,
            v_e_x27_4315_,
            v___x_4316_,
            v_arg_4317_,
            v_arg_4318_,
            v_e_4319_,
            v_proof_4320_,
            v___x_18465__boxed_4333_,
            v_contextDependent_18466__boxed_4334_,
            v___y_4323_,
            v___y_4324_,
            v___y_4325_,
            v___y_4326_,
            v___y_4327_,
            v___y_4328_,
            v___y_4329_,
            v___y_4330_,
            v___y_4331_,
        );
    leanh::lean_dec(v___y_4331_);
    leanh::lean_dec_ref(v___y_4330_);
    leanh::lean_dec(v___y_4329_);
    leanh::lean_dec_ref(v___y_4328_);
    leanh::lean_dec(v___y_4327_);
    leanh::lean_dec_ref(v___y_4326_);
    leanh::lean_dec(v___y_4325_);
    leanh::lean_dec_ref(v___y_4324_);
    leanh::lean_dec(v___y_4323_);
    return v_res_4335_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = leanh::lean_box(0);
    v___x_4347_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__5;
    v___x_4348_ = l_Lean_mkConst(v___x_4347_, v___x_4346_);
    return v___x_4348_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(
    mut v___x_4355_: u8,
    mut v_e_4356_: *mut leanh::LeanObject,
    mut v___y_4357_: *mut leanh::LeanObject,
    mut v___y_4358_: *mut leanh::LeanObject,
    mut v___y_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
    mut v___y_4363_: *mut leanh::LeanObject,
    mut v___y_4364_: *mut leanh::LeanObject,
    mut v___y_4365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: u8 = 0;
    let mut v_arg_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v_arg_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: u8 = 0;
    let mut v_arg_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v_arg_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: u8 = 0;
    let mut v_arg_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: u8 = 0;
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4390_: u8 = 0;
    let mut v___x_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4395_: u8 = 0;
    let mut v___x_4396_: u8 = 0;
    let mut v___x_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4401_: u8 = 0;
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: u8 = 0;
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut v_a_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4419_: u8 = 0;
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4432_: u8 = 0;
    let mut v_a_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4436_: u8 = 0;
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4440_: u8 = 0;
    let mut v_e_x27_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4443_: u8 = 0;
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4451_: u8 = 0;
    let mut v___x_4452_: u8 = 0;
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4457_: u8 = 0;
    let mut v___x_4458_: u8 = 0;
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: u8 = 0;
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_a_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4482_: u8 = 0;
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4496_: u8 = 0;
    let mut v_a_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4500_: u8 = 0;
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4504_: u8 = 0;
    let mut v_isSharedCheck_4505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_4356_);
                v___x_4370_ = l_Lean_Expr_cleanupAnnotations(v_e_4356_);
                v___x_4371_ = l_Lean_Expr_isApp(v___x_4370_);
                if v___x_4371_ == 0 {
                    leanh::lean_dec_ref(v___x_4370_);
                    leanh::lean_dec_ref(v_e_4356_);
                    state = 1;
                    continue;
                } else {
                    v_arg_4372_ = leanh::lean_ctor_get(v___x_4370_, 1);
                    leanh::lean_inc_ref(v_arg_4372_);
                    v___x_4373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4370_);
                    v___x_4374_ = l_Lean_Expr_isApp(v___x_4373_);
                    if v___x_4374_ == 0 {
                        leanh::lean_dec_ref(v___x_4373_);
                        leanh::lean_dec_ref(v_arg_4372_);
                        leanh::lean_dec_ref(v_e_4356_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_4375_ = leanh::lean_ctor_get(v___x_4373_, 1);
                        leanh::lean_inc_ref(v_arg_4375_);
                        v___x_4376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4373_);
                        v___x_4377_ = l_Lean_Expr_isApp(v___x_4376_);
                        if v___x_4377_ == 0 {
                            leanh::lean_dec_ref(v___x_4376_);
                            leanh::lean_dec_ref(v_arg_4375_);
                            leanh::lean_dec_ref(v_arg_4372_);
                            leanh::lean_dec_ref(v_e_4356_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_4378_ = leanh::lean_ctor_get(v___x_4376_, 1);
                            leanh::lean_inc_ref(v_arg_4378_);
                            v___x_4379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4376_);
                            v___x_4380_ = l_Lean_Expr_isApp(v___x_4379_);
                            if v___x_4380_ == 0 {
                                leanh::lean_dec_ref(v___x_4379_);
                                leanh::lean_dec_ref(v_arg_4378_);
                                leanh::lean_dec_ref(v_arg_4375_);
                                leanh::lean_dec_ref(v_arg_4372_);
                                leanh::lean_dec_ref(v_e_4356_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_4381_ = leanh::lean_ctor_get(v___x_4379_, 1);
                                leanh::lean_inc_ref(v_arg_4381_);
                                v___x_4382_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4379_);
                                v___x_4383_ = l_Lean_Expr_isApp(v___x_4382_);
                                if v___x_4383_ == 0 {
                                    leanh::lean_dec_ref(v___x_4382_);
                                    leanh::lean_dec_ref(v_arg_4381_);
                                    leanh::lean_dec_ref(v_arg_4378_);
                                    leanh::lean_dec_ref(v_arg_4375_);
                                    leanh::lean_dec_ref(v_arg_4372_);
                                    leanh::lean_dec_ref(v_e_4356_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_4384_ = leanh::lean_ctor_get(v___x_4382_, 1);
                                    leanh::lean_inc_ref(v_arg_4384_);
                                    v___x_4385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4382_);
                                    v___x_4386_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__1;
                                    v___x_4387_ = l_Lean_Expr_isConstOf(v___x_4385_, v___x_4386_);
                                    if v___x_4387_ == 0 {
                                        leanh::lean_dec_ref(v___x_4385_);
                                        leanh::lean_dec_ref(v_arg_4384_);
                                        leanh::lean_dec_ref(v_arg_4381_);
                                        leanh::lean_dec_ref(v_arg_4378_);
                                        leanh::lean_dec_ref(v_arg_4375_);
                                        leanh::lean_dec_ref(v_arg_4372_);
                                        leanh::lean_dec_ref(v_e_4356_);
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v___y_4365_);
                                        leanh::lean_inc_ref(v___y_4364_);
                                        leanh::lean_inc(v___y_4363_);
                                        leanh::lean_inc_ref(v___y_4362_);
                                        leanh::lean_inc(v___y_4361_);
                                        leanh::lean_inc_ref(v___y_4360_);
                                        leanh::lean_inc(v___y_4359_);
                                        leanh::lean_inc_ref(v___y_4358_);
                                        leanh::lean_inc(v___y_4357_);
                                        leanh::lean_inc_ref(v_arg_4381_);
                                        v___x_4388_ = lean_sym_simp(
                                            v_arg_4381_,
                                            v___y_4357_,
                                            v___y_4358_,
                                            v___y_4359_,
                                            v___y_4360_,
                                            v___y_4361_,
                                            v___y_4362_,
                                            v___y_4363_,
                                            v___y_4364_,
                                            v___y_4365_,
                                        );
                                        if leanh::lean_obj_tag(v___x_4388_) == 0 {
                                            v_a_4389_ = leanh::lean_ctor_get(v___x_4388_, 0);
                                            leanh::lean_inc(v_a_4389_);
                                            leanh::lean_dec_ref_known(v___x_4388_, 1);
                                            if leanh::lean_obj_tag(v_a_4389_) == 0 {
                                                leanh::lean_dec_ref(v_e_4356_);
                                                v_contextDependent_4390_ =
                                                    leanh::lean_ctor_get_uint8(
                                                        v_a_4389_, 1 as u32,
                                                    );
                                                leanh::lean_dec_ref_known(v_a_4389_, 0);
                                                v___x_4391_ = l_Lean_Meta_Sym_isTrueExpr___redArg(
                                                    v_arg_4381_,
                                                    v___y_4360_,
                                                );
                                                if leanh::lean_obj_tag(v___x_4391_) == 0 {
                                                    v_a_4392_ =
                                                        leanh::lean_ctor_get(v___x_4391_, 0);
                                                    v_isSharedCheck_4432_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4391_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4432_ == 0 {
                                                        v___x_4394_ = v___x_4391_;
                                                        v_isShared_4395_ = v_isSharedCheck_4432_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4392_);
                                                        leanh::lean_dec(v___x_4391_);
                                                        v___x_4394_ = leanh::lean_box(0);
                                                        v_isShared_4395_ = v_isSharedCheck_4432_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_4385_);
                                                    leanh::lean_dec_ref(v_arg_4384_);
                                                    leanh::lean_dec_ref(v_arg_4381_);
                                                    leanh::lean_dec_ref(v_arg_4378_);
                                                    leanh::lean_dec_ref(v_arg_4375_);
                                                    leanh::lean_dec_ref(v_arg_4372_);
                                                    v_a_4433_ =
                                                        leanh::lean_ctor_get(v___x_4391_, 0);
                                                    v_isSharedCheck_4440_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4391_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4440_ == 0 {
                                                        v___x_4435_ = v___x_4391_;
                                                        v_isShared_4436_ = v_isSharedCheck_4440_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4433_);
                                                        leanh::lean_dec(v___x_4391_);
                                                        v___x_4435_ = leanh::lean_box(0);
                                                        v_isShared_4436_ = v_isSharedCheck_4440_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v_e_x27_4441_ =
                                                    leanh::lean_ctor_get(v_a_4389_, 0);
                                                v_proof_4442_ =
                                                    leanh::lean_ctor_get(v_a_4389_, 1);
                                                v_contextDependent_4443_ =
                                                    leanh::lean_ctor_get_uint8(
                                                        v_a_4389_,
                                                        (core::mem::size_of::<
                                                            *mut leanh::LeanObject,
                                                        >(
                                                        ) * 2
                                                            + 1)
                                                            as u32,
                                                    );
                                                v_isSharedCheck_4505_ =
                                                    (!leanh::lean_is_exclusive(v_a_4389_))
                                                        as u8;
                                                if v_isSharedCheck_4505_ == 0 {
                                                    v___x_4445_ = v_a_4389_;
                                                    v_isShared_4446_ = v_isSharedCheck_4505_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_proof_4442_);
                                                    leanh::lean_inc(v_e_x27_4441_);
                                                    leanh::lean_dec(v_a_4389_);
                                                    v___x_4445_ = leanh::lean_box(0);
                                                    v_isShared_4446_ = v_isSharedCheck_4505_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_4385_);
                                            leanh::lean_dec_ref(v_arg_4384_);
                                            leanh::lean_dec_ref(v_arg_4381_);
                                            leanh::lean_dec_ref(v_arg_4378_);
                                            leanh::lean_dec_ref(v_arg_4375_);
                                            leanh::lean_dec_ref(v_arg_4372_);
                                            leanh::lean_dec_ref(v_e_4356_);
                                            return v___x_4388_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4368_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                leanh::lean_ctor_set_uint8(v___x_4368_, 0 as u32, v___x_4355_);
                leanh::lean_ctor_set_uint8(v___x_4368_, 1 as u32, v___x_4355_);
                v___x_4369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4369_, 0, v___x_4368_);
                return v___x_4369_;
            }
            2 => {
                v___x_4396_ = (leanh::lean_unbox(v_a_4392_) as u8);
                if v___x_4396_ == 0 {
                    leanh::lean_del_object(v___x_4394_);
                    v___x_4397_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_arg_4381_, v___y_4360_);
                    if leanh::lean_obj_tag(v___x_4397_) == 0 {
                        v_a_4398_ = leanh::lean_ctor_get(v___x_4397_, 0);
                        v_isSharedCheck_4415_ =
                            (!leanh::lean_is_exclusive(v___x_4397_)) as u8;
                        if v_isSharedCheck_4415_ == 0 {
                            v___x_4400_ = v___x_4397_;
                            v_isShared_4401_ = v_isSharedCheck_4415_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4398_);
                            leanh::lean_dec(v___x_4397_);
                            v___x_4400_ = leanh::lean_box(0);
                            v_isShared_4401_ = v_isSharedCheck_4415_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4392_);
                        leanh::lean_dec_ref(v___x_4385_);
                        leanh::lean_dec_ref(v_arg_4384_);
                        leanh::lean_dec_ref(v_arg_4381_);
                        leanh::lean_dec_ref(v_arg_4378_);
                        leanh::lean_dec_ref(v_arg_4375_);
                        leanh::lean_dec_ref(v_arg_4372_);
                        v_a_4416_ = leanh::lean_ctor_get(v___x_4397_, 0);
                        v_isSharedCheck_4423_ =
                            (!leanh::lean_is_exclusive(v___x_4397_)) as u8;
                        if v_isSharedCheck_4423_ == 0 {
                            v___x_4418_ = v___x_4397_;
                            v_isShared_4419_ = v_isSharedCheck_4423_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4416_);
                            leanh::lean_dec(v___x_4397_);
                            v___x_4418_ = leanh::lean_box(0);
                            v_isShared_4419_ = v_isSharedCheck_4423_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4392_);
                    leanh::lean_dec_ref(v_arg_4381_);
                    leanh::lean_dec_ref(v_arg_4378_);
                    v___x_4424_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__3;
                    v___x_4425_ = l_Lean_Expr_constLevels_x21(v___x_4385_);
                    leanh::lean_dec_ref(v___x_4385_);
                    v___x_4426_ = l_Lean_mkConst(v___x_4424_, v___x_4425_);
                    leanh::lean_inc_ref(v_arg_4375_);
                    v___x_4427_ = l_Lean_mkApp3(v___x_4426_, v_arg_4384_, v_arg_4375_, v_arg_4372_);
                    v___x_4428_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v___x_4428_, 0, v_arg_4375_);
                    leanh::lean_ctor_set(v___x_4428_, 1, v___x_4427_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4428_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_4355_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4428_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_4390_,
                    );
                    if v_isShared_4395_ == 0 {
                        leanh::lean_ctor_set(v___x_4394_, 0, v___x_4428_);
                        v___x_4430_ = v___x_4394_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4431_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
                        v___x_4430_ = v_reuseFailAlloc_4431_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4402_ = (leanh::lean_unbox(v_a_4398_) as u8);
                leanh::lean_dec(v_a_4398_);
                if v___x_4402_ == 0 {
                    leanh::lean_del_object(v___x_4400_);
                    leanh::lean_dec(v_a_4392_);
                    v___x_4403_ =
                        l_Lean_Meta_Sym_Simp_mkRflResult(v___x_4387_, v_contextDependent_4390_);
                    v___f_4404_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                    leanh::lean_closure_set(v___f_4404_, 0, v___x_4403_);
                    v___x_4405_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_4385_, v_arg_4384_, v_arg_4381_, v_arg_4378_, v_arg_4375_, v_arg_4372_, v___f_4404_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
                    leanh::lean_dec_ref(v___x_4385_);
                    return v___x_4405_;
                } else {
                    leanh::lean_dec_ref(v_arg_4381_);
                    leanh::lean_dec_ref(v_arg_4378_);
                    v___x_4406_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__2;
                    v___x_4407_ = l_Lean_Expr_constLevels_x21(v___x_4385_);
                    leanh::lean_dec_ref(v___x_4385_);
                    v___x_4408_ = l_Lean_mkConst(v___x_4406_, v___x_4407_);
                    leanh::lean_inc_ref(v_arg_4372_);
                    v___x_4409_ = l_Lean_mkApp3(v___x_4408_, v_arg_4384_, v_arg_4375_, v_arg_4372_);
                    v___x_4410_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v___x_4410_, 0, v_arg_4372_);
                    leanh::lean_ctor_set(v___x_4410_, 1, v___x_4409_);
                    v___x_4411_ = (leanh::lean_unbox(v_a_4392_) as u8);
                    leanh::lean_dec(v_a_4392_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4410_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v___x_4411_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_4410_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_4390_,
                    );
                    if v_isShared_4401_ == 0 {
                        leanh::lean_ctor_set(v___x_4400_, 0, v___x_4410_);
                        v___x_4413_ = v___x_4400_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4414_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v___x_4410_);
                        v___x_4413_ = v_reuseFailAlloc_4414_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4413_;
            }
            5 => {
                if v_isShared_4419_ == 0 {
                    v___x_4421_ = v___x_4418_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4422_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
                    v___x_4421_ = v_reuseFailAlloc_4422_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4421_;
            }
            7 => {
                return v___x_4430_;
            }
            8 => {
                if v_isShared_4436_ == 0 {
                    v___x_4438_ = v___x_4435_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4439_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
                    v___x_4438_ = v_reuseFailAlloc_4439_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4438_;
            }
            10 => {
                v___x_4447_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_4441_, v___y_4360_);
                if leanh::lean_obj_tag(v___x_4447_) == 0 {
                    v_a_4448_ = leanh::lean_ctor_get(v___x_4447_, 0);
                    v_isSharedCheck_4496_ = (!leanh::lean_is_exclusive(v___x_4447_)) as u8;
                    if v_isSharedCheck_4496_ == 0 {
                        v___x_4450_ = v___x_4447_;
                        v_isShared_4451_ = v_isSharedCheck_4496_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4448_);
                        leanh::lean_dec(v___x_4447_);
                        v___x_4450_ = leanh::lean_box(0);
                        v_isShared_4451_ = v_isSharedCheck_4496_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4445_);
                    leanh::lean_dec_ref(v_proof_4442_);
                    leanh::lean_dec_ref(v_e_x27_4441_);
                    leanh::lean_dec_ref(v___x_4385_);
                    leanh::lean_dec_ref(v_arg_4384_);
                    leanh::lean_dec_ref(v_arg_4381_);
                    leanh::lean_dec_ref(v_arg_4378_);
                    leanh::lean_dec_ref(v_arg_4375_);
                    leanh::lean_dec_ref(v_arg_4372_);
                    leanh::lean_dec_ref(v_e_4356_);
                    v_a_4497_ = leanh::lean_ctor_get(v___x_4447_, 0);
                    v_isSharedCheck_4504_ = (!leanh::lean_is_exclusive(v___x_4447_)) as u8;
                    if v_isSharedCheck_4504_ == 0 {
                        v___x_4499_ = v___x_4447_;
                        v_isShared_4500_ = v_isSharedCheck_4504_;
                        state = 19;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4497_);
                        leanh::lean_dec(v___x_4447_);
                        v___x_4499_ = leanh::lean_box(0);
                        v_isShared_4500_ = v_isSharedCheck_4504_;
                        state = 19;
                        continue;
                    }
                }
            }
            11 => {
                v___x_4452_ = (leanh::lean_unbox(v_a_4448_) as u8);
                if v___x_4452_ == 0 {
                    leanh::lean_del_object(v___x_4450_);
                    v___x_4453_ = l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_4441_, v___y_4360_);
                    if leanh::lean_obj_tag(v___x_4453_) == 0 {
                        v_a_4454_ = leanh::lean_ctor_get(v___x_4453_, 0);
                        v_isSharedCheck_4478_ =
                            (!leanh::lean_is_exclusive(v___x_4453_)) as u8;
                        if v_isSharedCheck_4478_ == 0 {
                            v___x_4456_ = v___x_4453_;
                            v_isShared_4457_ = v_isSharedCheck_4478_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4454_);
                            leanh::lean_dec(v___x_4453_);
                            v___x_4456_ = leanh::lean_box(0);
                            v_isShared_4457_ = v_isSharedCheck_4478_;
                            state = 12;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4448_);
                        leanh::lean_del_object(v___x_4445_);
                        leanh::lean_dec_ref(v_proof_4442_);
                        leanh::lean_dec_ref(v_e_x27_4441_);
                        leanh::lean_dec_ref(v___x_4385_);
                        leanh::lean_dec_ref(v_arg_4384_);
                        leanh::lean_dec_ref(v_arg_4381_);
                        leanh::lean_dec_ref(v_arg_4378_);
                        leanh::lean_dec_ref(v_arg_4375_);
                        leanh::lean_dec_ref(v_arg_4372_);
                        leanh::lean_dec_ref(v_e_4356_);
                        v_a_4479_ = leanh::lean_ctor_get(v___x_4453_, 0);
                        v_isSharedCheck_4486_ =
                            (!leanh::lean_is_exclusive(v___x_4453_)) as u8;
                        if v_isSharedCheck_4486_ == 0 {
                            v___x_4481_ = v___x_4453_;
                            v_isShared_4482_ = v_isSharedCheck_4486_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4479_);
                            leanh::lean_dec(v___x_4453_);
                            v___x_4481_ = leanh::lean_box(0);
                            v_isShared_4482_ = v_isSharedCheck_4486_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_4448_);
                    leanh::lean_dec_ref(v_e_x27_4441_);
                    leanh::lean_dec_ref(v___x_4385_);
                    leanh::lean_dec_ref(v_arg_4384_);
                    leanh::lean_dec_ref(v_arg_4381_);
                    leanh::lean_dec_ref(v_arg_4378_);
                    leanh::lean_dec_ref(v_arg_4372_);
                    v___x_4487_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__10;
                    v___x_4488_ = l_Lean_Expr_replaceFn(v_e_4356_, v___x_4487_);
                    v___x_4489_ = l_Lean_Expr_app___override(v___x_4488_, v_proof_4442_);
                    if v_isShared_4446_ == 0 {
                        leanh::lean_ctor_set(v___x_4445_, 1, v___x_4489_);
                        leanh::lean_ctor_set(v___x_4445_, 0, v_arg_4375_);
                        v___x_4491_ = v___x_4445_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4495_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_arg_4375_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4495_, 1, v___x_4489_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4495_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                            v_contextDependent_4443_,
                        );
                        v___x_4491_ = v_reuseFailAlloc_4495_;
                        state = 17;
                        continue;
                    }
                }
            }
            12 => {
                v___x_4458_ = (leanh::lean_unbox(v_a_4454_) as u8);
                leanh::lean_dec(v_a_4454_);
                if v___x_4458_ == 0 {
                    leanh::lean_del_object(v___x_4456_);
                    leanh::lean_dec(v_a_4448_);
                    leanh::lean_del_object(v___x_4445_);
                    v___x_4459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
                    leanh::lean_inc_ref_n(v_proof_4442_, 2);
                    leanh::lean_inc_ref_n(v_arg_4378_, 2);
                    leanh::lean_inc_ref_n(v_e_x27_4441_, 2);
                    leanh::lean_inc_ref_n(v_arg_4381_, 2);
                    v___x_4460_ = l_Lean_mkApp4(
                        v___x_4459_,
                        v_arg_4381_,
                        v_e_x27_4441_,
                        v_arg_4378_,
                        v_proof_4442_,
                    );
                    v___x_4461_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4462_ = l_Lean_Expr_getBoundedAppFn(v___x_4461_, v_e_4356_);
                    v___x_4463_ = leanh::lean_box((v___x_4387_) as usize);
                    v___x_4464_ = leanh::lean_box((v_contextDependent_4443_) as usize);
                    leanh::lean_inc_ref_n(v_arg_4372_, 2);
                    leanh::lean_inc_ref_n(v_arg_4375_, 2);
                    leanh::lean_inc_ref(v___x_4460_);
                    v___f_4465_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__1___boxed as *mut core::ffi::c_void, 19, 9);
                    leanh::lean_closure_set(v___f_4465_, 0, v___x_4462_);
                    leanh::lean_closure_set(v___f_4465_, 1, v_e_x27_4441_);
                    leanh::lean_closure_set(v___f_4465_, 2, v___x_4460_);
                    leanh::lean_closure_set(v___f_4465_, 3, v_arg_4375_);
                    leanh::lean_closure_set(v___f_4465_, 4, v_arg_4372_);
                    leanh::lean_closure_set(v___f_4465_, 5, v_e_4356_);
                    leanh::lean_closure_set(v___f_4465_, 6, v_proof_4442_);
                    leanh::lean_closure_set(v___f_4465_, 7, v___x_4463_);
                    leanh::lean_closure_set(v___f_4465_, 8, v___x_4464_);
                    leanh::lean_inc_ref(v_arg_4384_);
                    leanh::lean_inc_ref(v___x_4385_);
                    v___x_4466_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidableCongr___boxed as *mut core::ffi::c_void, 20, 10);
                    leanh::lean_closure_set(v___x_4466_, 0, v___x_4385_);
                    leanh::lean_closure_set(v___x_4466_, 1, v_arg_4384_);
                    leanh::lean_closure_set(v___x_4466_, 2, v_arg_4381_);
                    leanh::lean_closure_set(v___x_4466_, 3, v_arg_4378_);
                    leanh::lean_closure_set(v___x_4466_, 4, v_arg_4375_);
                    leanh::lean_closure_set(v___x_4466_, 5, v_arg_4372_);
                    leanh::lean_closure_set(v___x_4466_, 6, v_e_x27_4441_);
                    leanh::lean_closure_set(v___x_4466_, 7, v_proof_4442_);
                    leanh::lean_closure_set(v___x_4466_, 8, v___x_4460_);
                    leanh::lean_closure_set(v___x_4466_, 9, v___f_4465_);
                    v___x_4467_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchIteDecidable(v___x_4385_, v_arg_4384_, v_arg_4381_, v_arg_4378_, v_arg_4375_, v_arg_4372_, v___x_4466_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
                    leanh::lean_dec_ref(v___x_4385_);
                    return v___x_4467_;
                } else {
                    leanh::lean_dec_ref(v_e_x27_4441_);
                    leanh::lean_dec_ref(v___x_4385_);
                    leanh::lean_dec_ref(v_arg_4384_);
                    leanh::lean_dec_ref(v_arg_4381_);
                    leanh::lean_dec_ref(v_arg_4378_);
                    leanh::lean_dec_ref(v_arg_4375_);
                    v___x_4468_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__8;
                    v___x_4469_ = l_Lean_Expr_replaceFn(v_e_4356_, v___x_4468_);
                    v___x_4470_ = l_Lean_Expr_app___override(v___x_4469_, v_proof_4442_);
                    if v_isShared_4446_ == 0 {
                        leanh::lean_ctor_set(v___x_4445_, 1, v___x_4470_);
                        leanh::lean_ctor_set(v___x_4445_, 0, v_arg_4372_);
                        v___x_4472_ = v___x_4445_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4477_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_arg_4372_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 1, v___x_4470_);
                        v___x_4472_ = v_reuseFailAlloc_4477_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                v___x_4473_ = (leanh::lean_unbox(v_a_4448_) as u8);
                leanh::lean_dec(v_a_4448_);
                leanh::lean_ctor_set_uint8(
                    v___x_4472_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4473_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4472_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_4443_,
                );
                if v_isShared_4457_ == 0 {
                    leanh::lean_ctor_set(v___x_4456_, 0, v___x_4472_);
                    v___x_4475_ = v___x_4456_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4476_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4472_);
                    v___x_4475_ = v_reuseFailAlloc_4476_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4475_;
            }
            15 => {
                if v_isShared_4482_ == 0 {
                    v___x_4484_ = v___x_4481_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4485_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
                    v___x_4484_ = v_reuseFailAlloc_4485_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4484_;
            }
            17 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4491_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4355_,
                );
                if v_isShared_4451_ == 0 {
                    leanh::lean_ctor_set(v___x_4450_, 0, v___x_4491_);
                    v___x_4493_ = v___x_4450_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4494_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4494_, 0, v___x_4491_);
                    v___x_4493_ = v_reuseFailAlloc_4494_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4493_;
            }
            19 => {
                if v_isShared_4500_ == 0 {
                    v___x_4502_ = v___x_4499_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4497_);
                    v___x_4502_ = v_reuseFailAlloc_4503_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed(
    mut v___x_4506_: *mut leanh::LeanObject,
    mut v_e_4507_: *mut leanh::LeanObject,
    mut v___y_4508_: *mut leanh::LeanObject,
    mut v___y_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
    mut v___y_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_18600__boxed_4518_: u8 = 0;
    let mut v_res_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_18600__boxed_4518_ = (leanh::lean_unbox(v___x_4506_) as u8);
    v_res_4519_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2(
            v___x_18600__boxed_4518_,
            v_e_4507_,
            v___y_4508_,
            v___y_4509_,
            v___y_4510_,
            v___y_4511_,
            v___y_4512_,
            v___y_4513_,
            v___y_4514_,
            v___y_4515_,
            v___y_4516_,
        );
    leanh::lean_dec(v___y_4516_);
    leanh::lean_dec_ref(v___y_4515_);
    leanh::lean_dec(v___y_4514_);
    leanh::lean_dec_ref(v___y_4513_);
    leanh::lean_dec(v___y_4512_);
    leanh::lean_dec_ref(v___y_4511_);
    leanh::lean_dec(v___y_4510_);
    leanh::lean_dec_ref(v___y_4509_);
    leanh::lean_dec(v___y_4508_);
    return v_res_4519_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(
    mut v_e_4520_: *mut leanh::LeanObject,
    mut v_a_4521_: *mut leanh::LeanObject,
    mut v_a_4522_: *mut leanh::LeanObject,
    mut v_a_4523_: *mut leanh::LeanObject,
    mut v_a_4524_: *mut leanh::LeanObject,
    mut v_a_4525_: *mut leanh::LeanObject,
    mut v_a_4526_: *mut leanh::LeanObject,
    mut v_a_4527_: *mut leanh::LeanObject,
    mut v_a_4528_: *mut leanh::LeanObject,
    mut v_a_4529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numArgs_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: u8 = 0;
    v_numArgs_4531_ = l_Lean_Expr_getAppNumArgs(v_e_4520_);
    v___x_4532_ = leanh::lean_unsigned_to_nat(5);
    v___x_4533_ = lean_nat_dec_lt(v_numArgs_4531_, v___x_4532_);
    if v___x_4533_ == 0 {
        let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4534_ = leanh::lean_box((v___x_4533_) as usize);
        v___f_4535_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___boxed as *mut core::ffi::c_void, 12, 1);
        leanh::lean_closure_set(v___f_4535_, 0, v___x_4534_);
        v___x_4536_ = lean_nat_sub(v_numArgs_4531_, v___x_4532_);
        leanh::lean_dec(v_numArgs_4531_);
        v___x_4537_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(
            v_e_4520_,
            v___x_4536_,
            v___f_4535_,
            v_a_4521_,
            v_a_4522_,
            v_a_4523_,
            v_a_4524_,
            v_a_4525_,
            v_a_4526_,
            v_a_4527_,
            v_a_4528_,
            v_a_4529_,
        );
        leanh::lean_dec(v___x_4536_);
        return v___x_4537_;
    } else {
        let mut v___x_4538_: u8 = 0;
        let mut v___x_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_numArgs_4531_);
        leanh::lean_dec_ref(v_e_4520_);
        v___x_4538_ = 0;
        v___x_4539_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
        leanh::lean_ctor_set_uint8(v___x_4539_, 0 as u32, v___x_4533_);
        leanh::lean_ctor_set_uint8(v___x_4539_, 1 as u32, v___x_4538_);
        v___x_4540_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4540_, 0, v___x_4539_);
        return v___x_4540_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed(
    mut v_e_4541_: *mut leanh::LeanObject,
    mut v_a_4542_: *mut leanh::LeanObject,
    mut v_a_4543_: *mut leanh::LeanObject,
    mut v_a_4544_: *mut leanh::LeanObject,
    mut v_a_4545_: *mut leanh::LeanObject,
    mut v_a_4546_: *mut leanh::LeanObject,
    mut v_a_4547_: *mut leanh::LeanObject,
    mut v_a_4548_: *mut leanh::LeanObject,
    mut v_a_4549_: *mut leanh::LeanObject,
    mut v_a_4550_: *mut leanh::LeanObject,
    mut v_a_4551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4552_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv(
        v_e_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_, v_a_4547_, v_a_4548_,
        v_a_4549_, v_a_4550_,
    );
    leanh::lean_dec(v_a_4550_);
    leanh::lean_dec_ref(v_a_4549_);
    leanh::lean_dec(v_a_4548_);
    leanh::lean_dec_ref(v_a_4547_);
    leanh::lean_dec(v_a_4546_);
    leanh::lean_dec_ref(v_a_4545_);
    leanh::lean_dec(v_a_4544_);
    leanh::lean_dec_ref(v_a_4543_);
    leanh::lean_dec(v_a_4542_);
    return v_res_4552_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(
    mut v_f_4553_: *mut leanh::LeanObject,
    mut v_a_4554_: *mut leanh::LeanObject,
    mut v___y_4555_: *mut leanh::LeanObject,
    mut v___y_4556_: *mut leanh::LeanObject,
    mut v___y_4557_: *mut leanh::LeanObject,
    mut v___y_4558_: *mut leanh::LeanObject,
    mut v___y_4559_: *mut leanh::LeanObject,
    mut v___y_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
    mut v___y_4562_: *mut leanh::LeanObject,
    mut v___y_4563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4565_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___redArg(v_f_4553_, v_a_4554_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_);
    return v___x_4565_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1___boxed(
    mut v_f_4566_: *mut leanh::LeanObject,
    mut v_a_4567_: *mut leanh::LeanObject,
    mut v___y_4568_: *mut leanh::LeanObject,
    mut v___y_4569_: *mut leanh::LeanObject,
    mut v___y_4570_: *mut leanh::LeanObject,
    mut v___y_4571_: *mut leanh::LeanObject,
    mut v___y_4572_: *mut leanh::LeanObject,
    mut v___y_4573_: *mut leanh::LeanObject,
    mut v___y_4574_: *mut leanh::LeanObject,
    mut v___y_4575_: *mut leanh::LeanObject,
    mut v___y_4576_: *mut leanh::LeanObject,
    mut v___y_4577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4578_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__1(v_f_4566_, v_a_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4575_, v___y_4576_);
    leanh::lean_dec(v___y_4576_);
    leanh::lean_dec_ref(v___y_4575_);
    leanh::lean_dec(v___y_4574_);
    leanh::lean_dec_ref(v___y_4573_);
    leanh::lean_dec(v___y_4572_);
    leanh::lean_dec_ref(v___y_4571_);
    leanh::lean_dec(v___y_4570_);
    leanh::lean_dec_ref(v___y_4569_);
    leanh::lean_dec(v___y_4568_);
    return v_res_4578_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_;
    v___x_4637_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__20_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_;
    v___x_4638_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed
            as *mut core::ffi::c_void,
        11,
        0,
    );
    v___x_4639_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_4636_, v___x_4637_, v___x_4638_);
    return v___x_4639_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16____boxed(
    mut v_a_4640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4641_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_();
    return v_res_4641_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_()
-> *mut leanh::LeanObject {
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: u8 = 0;
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4643_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24___closed__18_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_;
    v___x_4644_ = 0;
    v___x_4645_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___boxed
            as *mut core::ffi::c_void,
        11,
        0,
    );
    v___x_4646_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_4643_, v___x_4644_, v___x_4645_);
    return v___x_4646_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18____boxed(
    mut v_a_4647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4648_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_();
    return v_res_4648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(
    mut v_f_4659_: *mut leanh::LeanObject,
    mut v_00_u03b1_4660_: *mut leanh::LeanObject,
    mut v_c_4661_: *mut leanh::LeanObject,
    mut v_inst_4662_: *mut leanh::LeanObject,
    mut v_a_4663_: *mut leanh::LeanObject,
    mut v_b_4664_: *mut leanh::LeanObject,
    mut v_instToMatch_4665_: *mut leanh::LeanObject,
    mut v_fallback_4666_: *mut leanh::LeanObject,
    mut v_a_4667_: *mut leanh::LeanObject,
    mut v_a_4668_: *mut leanh::LeanObject,
    mut v_a_4669_: *mut leanh::LeanObject,
    mut v_a_4670_: *mut leanh::LeanObject,
    mut v_a_4671_: *mut leanh::LeanObject,
    mut v_a_4672_: *mut leanh::LeanObject,
    mut v_a_4673_: *mut leanh::LeanObject,
    mut v_a_4674_: *mut leanh::LeanObject,
    mut v_a_4675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: u8 = 0;
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4700_: u8 = 0;
    let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4709_: u8 = 0;
    let mut v_a_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4713_: u8 = 0;
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4717_: u8 = 0;
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: u8 = 0;
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4727_: u8 = 0;
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_a_4737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4740_: u8 = 0;
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4744_: u8 = 0;
    let mut v_a_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4748_: u8 = 0;
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4677_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_4665_, v_a_4673_);
                if leanh::lean_obj_tag(v___x_4677_) == 0 {
                    v_a_4678_ = leanh::lean_ctor_get(v___x_4677_, 0);
                    leanh::lean_inc(v_a_4678_);
                    leanh::lean_dec_ref_known(v___x_4677_, 1);
                    v___x_4679_ = l_Lean_Expr_cleanupAnnotations(v_a_4678_);
                    v___x_4680_ = l_Lean_Expr_isApp(v___x_4679_);
                    if v___x_4680_ == 0 {
                        leanh::lean_dec_ref(v___x_4679_);
                        leanh::lean_dec_ref(v_b_4664_);
                        leanh::lean_dec_ref(v_a_4663_);
                        leanh::lean_dec_ref(v_inst_4662_);
                        leanh::lean_dec_ref(v_c_4661_);
                        leanh::lean_dec_ref(v_00_u03b1_4660_);
                        leanh::lean_inc(v_a_4675_);
                        leanh::lean_inc_ref(v_a_4674_);
                        leanh::lean_inc(v_a_4673_);
                        leanh::lean_inc_ref(v_a_4672_);
                        leanh::lean_inc(v_a_4671_);
                        leanh::lean_inc_ref(v_a_4670_);
                        leanh::lean_inc(v_a_4669_);
                        leanh::lean_inc_ref(v_a_4668_);
                        leanh::lean_inc(v_a_4667_);
                        v___x_4681_ = leanh::lean_apply_10(
                            v_fallback_4666_,
                            v_a_4667_,
                            v_a_4668_,
                            v_a_4669_,
                            v_a_4670_,
                            v_a_4671_,
                            v_a_4672_,
                            v_a_4673_,
                            v_a_4674_,
                            v_a_4675_,
                            leanh::lean_box(0),
                        );
                        return v___x_4681_;
                    } else {
                        v_arg_4682_ = leanh::lean_ctor_get(v___x_4679_, 1);
                        leanh::lean_inc_ref(v_arg_4682_);
                        v___x_4683_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4679_);
                        v___x_4684_ = l_Lean_Expr_isApp(v___x_4683_);
                        if v___x_4684_ == 0 {
                            leanh::lean_dec_ref(v___x_4683_);
                            leanh::lean_dec_ref(v_arg_4682_);
                            leanh::lean_dec_ref(v_b_4664_);
                            leanh::lean_dec_ref(v_a_4663_);
                            leanh::lean_dec_ref(v_inst_4662_);
                            leanh::lean_dec_ref(v_c_4661_);
                            leanh::lean_dec_ref(v_00_u03b1_4660_);
                            leanh::lean_inc(v_a_4675_);
                            leanh::lean_inc_ref(v_a_4674_);
                            leanh::lean_inc(v_a_4673_);
                            leanh::lean_inc_ref(v_a_4672_);
                            leanh::lean_inc(v_a_4671_);
                            leanh::lean_inc_ref(v_a_4670_);
                            leanh::lean_inc(v_a_4669_);
                            leanh::lean_inc_ref(v_a_4668_);
                            leanh::lean_inc(v_a_4667_);
                            v___x_4685_ = leanh::lean_apply_10(
                                v_fallback_4666_,
                                v_a_4667_,
                                v_a_4668_,
                                v_a_4669_,
                                v_a_4670_,
                                v_a_4671_,
                                v_a_4672_,
                                v_a_4673_,
                                v_a_4674_,
                                v_a_4675_,
                                leanh::lean_box(0),
                            );
                            return v___x_4685_;
                        } else {
                            v___x_4686_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4683_);
                            v___x_4687_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1;
                            v___x_4688_ = l_Lean_Expr_isConstOf(v___x_4686_, v___x_4687_);
                            if v___x_4688_ == 0 {
                                v___x_4689_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3;
                                v___x_4690_ = l_Lean_Expr_isConstOf(v___x_4686_, v___x_4689_);
                                leanh::lean_dec_ref(v___x_4686_);
                                if v___x_4690_ == 0 {
                                    leanh::lean_dec_ref(v_arg_4682_);
                                    leanh::lean_dec_ref(v_b_4664_);
                                    leanh::lean_dec_ref(v_a_4663_);
                                    leanh::lean_dec_ref(v_inst_4662_);
                                    leanh::lean_dec_ref(v_c_4661_);
                                    leanh::lean_dec_ref(v_00_u03b1_4660_);
                                    leanh::lean_inc(v_a_4675_);
                                    leanh::lean_inc_ref(v_a_4674_);
                                    leanh::lean_inc(v_a_4673_);
                                    leanh::lean_inc_ref(v_a_4672_);
                                    leanh::lean_inc(v_a_4671_);
                                    leanh::lean_inc_ref(v_a_4670_);
                                    leanh::lean_inc(v_a_4669_);
                                    leanh::lean_inc_ref(v_a_4668_);
                                    leanh::lean_inc(v_a_4667_);
                                    v___x_4691_ = leanh::lean_apply_10(
                                        v_fallback_4666_,
                                        v_a_4667_,
                                        v_a_4668_,
                                        v_a_4669_,
                                        v_a_4670_,
                                        v_a_4671_,
                                        v_a_4672_,
                                        v_a_4673_,
                                        v_a_4674_,
                                        v_a_4675_,
                                        leanh::lean_box(0),
                                    );
                                    return v___x_4691_;
                                } else {
                                    leanh::lean_dec_ref(v_fallback_4666_);
                                    v___x_4692_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_4693_ = lean_mk_empty_array_with_capacity(v___x_4692_);
                                    leanh::lean_inc_ref(v_arg_4682_);
                                    v___x_4694_ = lean_array_push(v___x_4693_, v_arg_4682_);
                                    leanh::lean_inc_ref(v_a_4663_);
                                    v___x_4695_ = l_Lean_Expr_betaRev(
                                        v_a_4663_,
                                        v___x_4694_,
                                        v___x_4688_,
                                        v___x_4688_,
                                    );
                                    leanh::lean_dec_ref(v___x_4694_);
                                    v___x_4696_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                        v___x_4695_,
                                        v_a_4671_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4696_) == 0 {
                                        v_a_4697_ = leanh::lean_ctor_get(v___x_4696_, 0);
                                        v_isSharedCheck_4709_ =
                                            (!leanh::lean_is_exclusive(v___x_4696_)) as u8;
                                        if v_isSharedCheck_4709_ == 0 {
                                            v___x_4699_ = v___x_4696_;
                                            v_isShared_4700_ = v_isSharedCheck_4709_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4697_);
                                            leanh::lean_dec(v___x_4696_);
                                            v___x_4699_ = leanh::lean_box(0);
                                            v_isShared_4700_ = v_isSharedCheck_4709_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_arg_4682_);
                                        leanh::lean_dec_ref(v_b_4664_);
                                        leanh::lean_dec_ref(v_a_4663_);
                                        leanh::lean_dec_ref(v_inst_4662_);
                                        leanh::lean_dec_ref(v_c_4661_);
                                        leanh::lean_dec_ref(v_00_u03b1_4660_);
                                        v_a_4710_ = leanh::lean_ctor_get(v___x_4696_, 0);
                                        v_isSharedCheck_4717_ =
                                            (!leanh::lean_is_exclusive(v___x_4696_)) as u8;
                                        if v_isSharedCheck_4717_ == 0 {
                                            v___x_4712_ = v___x_4696_;
                                            v_isShared_4713_ = v_isSharedCheck_4717_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4710_);
                                            leanh::lean_dec(v___x_4696_);
                                            v___x_4712_ = leanh::lean_box(0);
                                            v_isShared_4713_ = v_isSharedCheck_4717_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4686_);
                                leanh::lean_dec_ref(v_fallback_4666_);
                                v___x_4718_ = leanh::lean_unsigned_to_nat(1);
                                v___x_4719_ = lean_mk_empty_array_with_capacity(v___x_4718_);
                                leanh::lean_inc_ref(v_arg_4682_);
                                v___x_4720_ = lean_array_push(v___x_4719_, v_arg_4682_);
                                v___x_4721_ = 0;
                                leanh::lean_inc_ref(v_b_4664_);
                                v___x_4722_ = l_Lean_Expr_betaRev(
                                    v_b_4664_,
                                    v___x_4720_,
                                    v___x_4721_,
                                    v___x_4721_,
                                );
                                leanh::lean_dec_ref(v___x_4720_);
                                v___x_4723_ =
                                    l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_4722_, v_a_4671_);
                                if leanh::lean_obj_tag(v___x_4723_) == 0 {
                                    v_a_4724_ = leanh::lean_ctor_get(v___x_4723_, 0);
                                    v_isSharedCheck_4736_ =
                                        (!leanh::lean_is_exclusive(v___x_4723_)) as u8;
                                    if v_isSharedCheck_4736_ == 0 {
                                        v___x_4726_ = v___x_4723_;
                                        v_isShared_4727_ = v_isSharedCheck_4736_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4724_);
                                        leanh::lean_dec(v___x_4723_);
                                        v___x_4726_ = leanh::lean_box(0);
                                        v_isShared_4727_ = v_isSharedCheck_4736_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_4682_);
                                    leanh::lean_dec_ref(v_b_4664_);
                                    leanh::lean_dec_ref(v_a_4663_);
                                    leanh::lean_dec_ref(v_inst_4662_);
                                    leanh::lean_dec_ref(v_c_4661_);
                                    leanh::lean_dec_ref(v_00_u03b1_4660_);
                                    v_a_4737_ = leanh::lean_ctor_get(v___x_4723_, 0);
                                    v_isSharedCheck_4744_ =
                                        (!leanh::lean_is_exclusive(v___x_4723_)) as u8;
                                    if v_isSharedCheck_4744_ == 0 {
                                        v___x_4739_ = v___x_4723_;
                                        v_isShared_4740_ = v_isSharedCheck_4744_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4737_);
                                        leanh::lean_dec(v___x_4723_);
                                        v___x_4739_ = leanh::lean_box(0);
                                        v_isShared_4740_ = v_isSharedCheck_4744_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_4666_);
                    leanh::lean_dec_ref(v_b_4664_);
                    leanh::lean_dec_ref(v_a_4663_);
                    leanh::lean_dec_ref(v_inst_4662_);
                    leanh::lean_dec_ref(v_c_4661_);
                    leanh::lean_dec_ref(v_00_u03b1_4660_);
                    v_a_4745_ = leanh::lean_ctor_get(v___x_4677_, 0);
                    v_isSharedCheck_4752_ = (!leanh::lean_is_exclusive(v___x_4677_)) as u8;
                    if v_isSharedCheck_4752_ == 0 {
                        v___x_4747_ = v___x_4677_;
                        v_isShared_4748_ = v_isSharedCheck_4752_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4745_);
                        leanh::lean_dec(v___x_4677_);
                        v___x_4747_ = leanh::lean_box(0);
                        v_isShared_4748_ = v_isSharedCheck_4752_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4701_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__1;
                v___x_4702_ = l_Lean_Expr_constLevels_x21(v_f_4659_);
                v___x_4703_ = l_Lean_mkConst(v___x_4701_, v___x_4702_);
                v___x_4704_ = l_Lean_mkApp6(
                    v___x_4703_,
                    v_00_u03b1_4660_,
                    v_c_4661_,
                    v_inst_4662_,
                    v_a_4663_,
                    v_b_4664_,
                    v_arg_4682_,
                );
                v___x_4705_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_4705_, 0, v_a_4697_);
                leanh::lean_ctor_set(v___x_4705_, 1, v___x_4704_);
                leanh::lean_ctor_set_uint8(
                    v___x_4705_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4688_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4705_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_4688_,
                );
                if v_isShared_4700_ == 0 {
                    leanh::lean_ctor_set(v___x_4699_, 0, v___x_4705_);
                    v___x_4707_ = v___x_4699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v___x_4705_);
                    v___x_4707_ = v_reuseFailAlloc_4708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4707_;
            }
            3 => {
                if v_isShared_4713_ == 0 {
                    v___x_4715_ = v___x_4712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4716_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
                    v___x_4715_ = v_reuseFailAlloc_4716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4715_;
            }
            5 => {
                v___x_4728_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___closed__3;
                v___x_4729_ = l_Lean_Expr_constLevels_x21(v_f_4659_);
                v___x_4730_ = l_Lean_mkConst(v___x_4728_, v___x_4729_);
                v___x_4731_ = l_Lean_mkApp6(
                    v___x_4730_,
                    v_00_u03b1_4660_,
                    v_c_4661_,
                    v_inst_4662_,
                    v_a_4663_,
                    v_b_4664_,
                    v_arg_4682_,
                );
                v___x_4732_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_4732_, 0, v_a_4724_);
                leanh::lean_ctor_set(v___x_4732_, 1, v___x_4731_);
                leanh::lean_ctor_set_uint8(
                    v___x_4732_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4721_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4732_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_4721_,
                );
                if v_isShared_4727_ == 0 {
                    leanh::lean_ctor_set(v___x_4726_, 0, v___x_4732_);
                    v___x_4734_ = v___x_4726_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4735_, 0, v___x_4732_);
                    v___x_4734_ = v_reuseFailAlloc_4735_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4734_;
            }
            7 => {
                if v_isShared_4740_ == 0 {
                    v___x_4742_ = v___x_4739_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4743_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
                    v___x_4742_ = v_reuseFailAlloc_4743_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4742_;
            }
            9 => {
                if v_isShared_4748_ == 0 {
                    v___x_4750_ = v___x_4747_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4751_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_a_4745_);
                    v___x_4750_ = v_reuseFailAlloc_4751_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4750_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_4753_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_4754_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_4755_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_4756_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_4757_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4758_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_instToMatch_4759_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_fallback_4760_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_4761_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_4762_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_4763_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_4764_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_4765_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_4766_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_4767_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_4768_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_4769_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_4770_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4771_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(
            v_f_4753_,
            v_00_u03b1_4754_,
            v_c_4755_,
            v_inst_4756_,
            v_a_4757_,
            v_b_4758_,
            v_instToMatch_4759_,
            v_fallback_4760_,
            v_a_4761_,
            v_a_4762_,
            v_a_4763_,
            v_a_4764_,
            v_a_4765_,
            v_a_4766_,
            v_a_4767_,
            v_a_4768_,
            v_a_4769_,
        );
    leanh::lean_dec(v_a_4769_);
    leanh::lean_dec_ref(v_a_4768_);
    leanh::lean_dec(v_a_4767_);
    leanh::lean_dec_ref(v_a_4766_);
    leanh::lean_dec(v_a_4765_);
    leanh::lean_dec_ref(v_a_4764_);
    leanh::lean_dec(v_a_4763_);
    leanh::lean_dec_ref(v_a_4762_);
    leanh::lean_dec(v_a_4761_);
    leanh::lean_dec_ref(v_f_4753_);
    return v_res_4771_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4777_ = leanh::lean_box(0);
    v___x_4778_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2;
    v___x_4779_ = l_Lean_mkConst(v___x_4778_, v___x_4777_);
    return v___x_4779_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4789_ = leanh::lean_box(0);
    v___x_4790_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7;
    v___x_4791_ = l_Lean_mkConst(v___x_4790_, v___x_4789_);
    return v___x_4791_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(
    mut v_f_4797_: *mut leanh::LeanObject,
    mut v_00_u03b1_4798_: *mut leanh::LeanObject,
    mut v_c_4799_: *mut leanh::LeanObject,
    mut v_inst_4800_: *mut leanh::LeanObject,
    mut v_a_4801_: *mut leanh::LeanObject,
    mut v_b_4802_: *mut leanh::LeanObject,
    mut v_c_x27_4803_: *mut leanh::LeanObject,
    mut v_h_4804_: *mut leanh::LeanObject,
    mut v_inst_x27_4805_: *mut leanh::LeanObject,
    mut v_fallback_4806_: *mut leanh::LeanObject,
    mut v_a_4807_: *mut leanh::LeanObject,
    mut v_a_4808_: *mut leanh::LeanObject,
    mut v_a_4809_: *mut leanh::LeanObject,
    mut v_a_4810_: *mut leanh::LeanObject,
    mut v_a_4811_: *mut leanh::LeanObject,
    mut v_a_4812_: *mut leanh::LeanObject,
    mut v_a_4813_: *mut leanh::LeanObject,
    mut v_a_4814_: *mut leanh::LeanObject,
    mut v_a_4815_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: u8 = 0;
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u8 = 0;
    let mut v___x_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: u8 = 0;
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: u8 = 0;
    let mut v___x_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4851_: u8 = 0;
    let mut v_a_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: u8 = 0;
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4871_: u8 = 0;
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_a_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4888_: u8 = 0;
    let mut v_a_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4892_: u8 = 0;
    let mut v___x_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4896_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4817_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_4805_, v_a_4813_);
                if leanh::lean_obj_tag(v___x_4817_) == 0 {
                    v_a_4818_ = leanh::lean_ctor_get(v___x_4817_, 0);
                    leanh::lean_inc(v_a_4818_);
                    leanh::lean_dec_ref_known(v___x_4817_, 1);
                    v___x_4819_ = l_Lean_Expr_cleanupAnnotations(v_a_4818_);
                    v___x_4820_ = l_Lean_Expr_isApp(v___x_4819_);
                    if v___x_4820_ == 0 {
                        leanh::lean_dec_ref(v___x_4819_);
                        leanh::lean_dec_ref(v_h_4804_);
                        leanh::lean_dec_ref(v_c_x27_4803_);
                        leanh::lean_dec_ref(v_b_4802_);
                        leanh::lean_dec_ref(v_a_4801_);
                        leanh::lean_dec_ref(v_inst_4800_);
                        leanh::lean_dec_ref(v_c_4799_);
                        leanh::lean_dec_ref(v_00_u03b1_4798_);
                        leanh::lean_inc(v_a_4815_);
                        leanh::lean_inc_ref(v_a_4814_);
                        leanh::lean_inc(v_a_4813_);
                        leanh::lean_inc_ref(v_a_4812_);
                        leanh::lean_inc(v_a_4811_);
                        leanh::lean_inc_ref(v_a_4810_);
                        leanh::lean_inc(v_a_4809_);
                        leanh::lean_inc_ref(v_a_4808_);
                        leanh::lean_inc(v_a_4807_);
                        v___x_4821_ = leanh::lean_apply_10(
                            v_fallback_4806_,
                            v_a_4807_,
                            v_a_4808_,
                            v_a_4809_,
                            v_a_4810_,
                            v_a_4811_,
                            v_a_4812_,
                            v_a_4813_,
                            v_a_4814_,
                            v_a_4815_,
                            leanh::lean_box(0),
                        );
                        return v___x_4821_;
                    } else {
                        v_arg_4822_ = leanh::lean_ctor_get(v___x_4819_, 1);
                        leanh::lean_inc_ref(v_arg_4822_);
                        v___x_4823_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4819_);
                        v___x_4824_ = l_Lean_Expr_isApp(v___x_4823_);
                        if v___x_4824_ == 0 {
                            leanh::lean_dec_ref(v___x_4823_);
                            leanh::lean_dec_ref(v_arg_4822_);
                            leanh::lean_dec_ref(v_h_4804_);
                            leanh::lean_dec_ref(v_c_x27_4803_);
                            leanh::lean_dec_ref(v_b_4802_);
                            leanh::lean_dec_ref(v_a_4801_);
                            leanh::lean_dec_ref(v_inst_4800_);
                            leanh::lean_dec_ref(v_c_4799_);
                            leanh::lean_dec_ref(v_00_u03b1_4798_);
                            leanh::lean_inc(v_a_4815_);
                            leanh::lean_inc_ref(v_a_4814_);
                            leanh::lean_inc(v_a_4813_);
                            leanh::lean_inc_ref(v_a_4812_);
                            leanh::lean_inc(v_a_4811_);
                            leanh::lean_inc_ref(v_a_4810_);
                            leanh::lean_inc(v_a_4809_);
                            leanh::lean_inc_ref(v_a_4808_);
                            leanh::lean_inc(v_a_4807_);
                            v___x_4825_ = leanh::lean_apply_10(
                                v_fallback_4806_,
                                v_a_4807_,
                                v_a_4808_,
                                v_a_4809_,
                                v_a_4810_,
                                v_a_4811_,
                                v_a_4812_,
                                v_a_4813_,
                                v_a_4814_,
                                v_a_4815_,
                                leanh::lean_box(0),
                            );
                            return v___x_4825_;
                        } else {
                            v___x_4826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4823_);
                            v___x_4827_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1;
                            v___x_4828_ = l_Lean_Expr_isConstOf(v___x_4826_, v___x_4827_);
                            if v___x_4828_ == 0 {
                                v___x_4829_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3;
                                v___x_4830_ = l_Lean_Expr_isConstOf(v___x_4826_, v___x_4829_);
                                leanh::lean_dec_ref(v___x_4826_);
                                if v___x_4830_ == 0 {
                                    leanh::lean_dec_ref(v_arg_4822_);
                                    leanh::lean_dec_ref(v_h_4804_);
                                    leanh::lean_dec_ref(v_c_x27_4803_);
                                    leanh::lean_dec_ref(v_b_4802_);
                                    leanh::lean_dec_ref(v_a_4801_);
                                    leanh::lean_dec_ref(v_inst_4800_);
                                    leanh::lean_dec_ref(v_c_4799_);
                                    leanh::lean_dec_ref(v_00_u03b1_4798_);
                                    leanh::lean_inc(v_a_4815_);
                                    leanh::lean_inc_ref(v_a_4814_);
                                    leanh::lean_inc(v_a_4813_);
                                    leanh::lean_inc_ref(v_a_4812_);
                                    leanh::lean_inc(v_a_4811_);
                                    leanh::lean_inc_ref(v_a_4810_);
                                    leanh::lean_inc(v_a_4809_);
                                    leanh::lean_inc_ref(v_a_4808_);
                                    leanh::lean_inc(v_a_4807_);
                                    v___x_4831_ = leanh::lean_apply_10(
                                        v_fallback_4806_,
                                        v_a_4807_,
                                        v_a_4808_,
                                        v_a_4809_,
                                        v_a_4810_,
                                        v_a_4811_,
                                        v_a_4812_,
                                        v_a_4813_,
                                        v_a_4814_,
                                        v_a_4815_,
                                        leanh::lean_box(0),
                                    );
                                    return v___x_4831_;
                                } else {
                                    leanh::lean_dec_ref(v_fallback_4806_);
                                    v___x_4832_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__3);
                                    leanh::lean_inc_ref(v_arg_4822_);
                                    leanh::lean_inc_ref(v_h_4804_);
                                    leanh::lean_inc_ref(v_c_x27_4803_);
                                    leanh::lean_inc_ref(v_c_4799_);
                                    v___x_4833_ = l_Lean_mkApp4(
                                        v___x_4832_,
                                        v_c_4799_,
                                        v_c_x27_4803_,
                                        v_h_4804_,
                                        v_arg_4822_,
                                    );
                                    v___x_4834_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_4835_ = lean_mk_empty_array_with_capacity(v___x_4834_);
                                    v___x_4836_ = lean_array_push(v___x_4835_, v___x_4833_);
                                    leanh::lean_inc_ref(v_a_4801_);
                                    v___x_4837_ = l_Lean_Expr_betaRev(
                                        v_a_4801_,
                                        v___x_4836_,
                                        v___x_4828_,
                                        v___x_4828_,
                                    );
                                    leanh::lean_dec_ref(v___x_4836_);
                                    v___x_4838_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                        v___x_4837_,
                                        v_a_4811_,
                                    );
                                    if leanh::lean_obj_tag(v___x_4838_) == 0 {
                                        v_a_4839_ = leanh::lean_ctor_get(v___x_4838_, 0);
                                        v_isSharedCheck_4851_ =
                                            (!leanh::lean_is_exclusive(v___x_4838_)) as u8;
                                        if v_isSharedCheck_4851_ == 0 {
                                            v___x_4841_ = v___x_4838_;
                                            v_isShared_4842_ = v_isSharedCheck_4851_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4839_);
                                            leanh::lean_dec(v___x_4838_);
                                            v___x_4841_ = leanh::lean_box(0);
                                            v_isShared_4842_ = v_isSharedCheck_4851_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_arg_4822_);
                                        leanh::lean_dec_ref(v_h_4804_);
                                        leanh::lean_dec_ref(v_c_x27_4803_);
                                        leanh::lean_dec_ref(v_b_4802_);
                                        leanh::lean_dec_ref(v_a_4801_);
                                        leanh::lean_dec_ref(v_inst_4800_);
                                        leanh::lean_dec_ref(v_c_4799_);
                                        leanh::lean_dec_ref(v_00_u03b1_4798_);
                                        v_a_4852_ = leanh::lean_ctor_get(v___x_4838_, 0);
                                        v_isSharedCheck_4859_ =
                                            (!leanh::lean_is_exclusive(v___x_4838_)) as u8;
                                        if v_isSharedCheck_4859_ == 0 {
                                            v___x_4854_ = v___x_4838_;
                                            v_isShared_4855_ = v_isSharedCheck_4859_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4852_);
                                            leanh::lean_dec(v___x_4838_);
                                            v___x_4854_ = leanh::lean_box(0);
                                            v_isShared_4855_ = v_isSharedCheck_4859_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4826_);
                                leanh::lean_dec_ref(v_fallback_4806_);
                                v___x_4860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__8);
                                leanh::lean_inc_ref(v_arg_4822_);
                                leanh::lean_inc_ref(v_h_4804_);
                                leanh::lean_inc_ref(v_c_x27_4803_);
                                leanh::lean_inc_ref(v_c_4799_);
                                v___x_4861_ = l_Lean_mkApp4(
                                    v___x_4860_,
                                    v_c_4799_,
                                    v_c_x27_4803_,
                                    v_h_4804_,
                                    v_arg_4822_,
                                );
                                v___x_4862_ = leanh::lean_unsigned_to_nat(1);
                                v___x_4863_ = lean_mk_empty_array_with_capacity(v___x_4862_);
                                v___x_4864_ = lean_array_push(v___x_4863_, v___x_4861_);
                                v___x_4865_ = 0;
                                leanh::lean_inc_ref(v_b_4802_);
                                v___x_4866_ = l_Lean_Expr_betaRev(
                                    v_b_4802_,
                                    v___x_4864_,
                                    v___x_4865_,
                                    v___x_4865_,
                                );
                                leanh::lean_dec_ref(v___x_4864_);
                                v___x_4867_ =
                                    l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_4866_, v_a_4811_);
                                if leanh::lean_obj_tag(v___x_4867_) == 0 {
                                    v_a_4868_ = leanh::lean_ctor_get(v___x_4867_, 0);
                                    v_isSharedCheck_4880_ =
                                        (!leanh::lean_is_exclusive(v___x_4867_)) as u8;
                                    if v_isSharedCheck_4880_ == 0 {
                                        v___x_4870_ = v___x_4867_;
                                        v_isShared_4871_ = v_isSharedCheck_4880_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4868_);
                                        leanh::lean_dec(v___x_4867_);
                                        v___x_4870_ = leanh::lean_box(0);
                                        v_isShared_4871_ = v_isSharedCheck_4880_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_4822_);
                                    leanh::lean_dec_ref(v_h_4804_);
                                    leanh::lean_dec_ref(v_c_x27_4803_);
                                    leanh::lean_dec_ref(v_b_4802_);
                                    leanh::lean_dec_ref(v_a_4801_);
                                    leanh::lean_dec_ref(v_inst_4800_);
                                    leanh::lean_dec_ref(v_c_4799_);
                                    leanh::lean_dec_ref(v_00_u03b1_4798_);
                                    v_a_4881_ = leanh::lean_ctor_get(v___x_4867_, 0);
                                    v_isSharedCheck_4888_ =
                                        (!leanh::lean_is_exclusive(v___x_4867_)) as u8;
                                    if v_isSharedCheck_4888_ == 0 {
                                        v___x_4883_ = v___x_4867_;
                                        v_isShared_4884_ = v_isSharedCheck_4888_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4881_);
                                        leanh::lean_dec(v___x_4867_);
                                        v___x_4883_ = leanh::lean_box(0);
                                        v_isShared_4884_ = v_isSharedCheck_4888_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_4806_);
                    leanh::lean_dec_ref(v_h_4804_);
                    leanh::lean_dec_ref(v_c_x27_4803_);
                    leanh::lean_dec_ref(v_b_4802_);
                    leanh::lean_dec_ref(v_a_4801_);
                    leanh::lean_dec_ref(v_inst_4800_);
                    leanh::lean_dec_ref(v_c_4799_);
                    leanh::lean_dec_ref(v_00_u03b1_4798_);
                    v_a_4889_ = leanh::lean_ctor_get(v___x_4817_, 0);
                    v_isSharedCheck_4896_ = (!leanh::lean_is_exclusive(v___x_4817_)) as u8;
                    if v_isSharedCheck_4896_ == 0 {
                        v___x_4891_ = v___x_4817_;
                        v_isShared_4892_ = v_isSharedCheck_4896_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4889_);
                        leanh::lean_dec(v___x_4817_);
                        v___x_4891_ = leanh::lean_box(0);
                        v_isShared_4892_ = v_isSharedCheck_4896_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4843_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__5;
                v___x_4844_ = l_Lean_Expr_constLevels_x21(v_f_4797_);
                v___x_4845_ = l_Lean_mkConst(v___x_4843_, v___x_4844_);
                v___x_4846_ = l_Lean_mkApp8(
                    v___x_4845_,
                    v_00_u03b1_4798_,
                    v_c_4799_,
                    v_inst_4800_,
                    v_a_4801_,
                    v_b_4802_,
                    v_c_x27_4803_,
                    v_h_4804_,
                    v_arg_4822_,
                );
                v___x_4847_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_4847_, 0, v_a_4839_);
                leanh::lean_ctor_set(v___x_4847_, 1, v___x_4846_);
                leanh::lean_ctor_set_uint8(
                    v___x_4847_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4828_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4847_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_4828_,
                );
                if v_isShared_4842_ == 0 {
                    leanh::lean_ctor_set(v___x_4841_, 0, v___x_4847_);
                    v___x_4849_ = v___x_4841_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4850_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
                    v___x_4849_ = v_reuseFailAlloc_4850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4849_;
            }
            3 => {
                if v_isShared_4855_ == 0 {
                    v___x_4857_ = v___x_4854_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4852_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4857_;
            }
            5 => {
                v___x_4872_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__10;
                v___x_4873_ = l_Lean_Expr_constLevels_x21(v_f_4797_);
                v___x_4874_ = l_Lean_mkConst(v___x_4872_, v___x_4873_);
                v___x_4875_ = l_Lean_mkApp8(
                    v___x_4874_,
                    v_00_u03b1_4798_,
                    v_c_4799_,
                    v_inst_4800_,
                    v_a_4801_,
                    v_b_4802_,
                    v_c_x27_4803_,
                    v_h_4804_,
                    v_arg_4822_,
                );
                v___x_4876_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_4876_, 0, v_a_4868_);
                leanh::lean_ctor_set(v___x_4876_, 1, v___x_4875_);
                leanh::lean_ctor_set_uint8(
                    v___x_4876_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_4865_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4876_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_4865_,
                );
                if v_isShared_4871_ == 0 {
                    leanh::lean_ctor_set(v___x_4870_, 0, v___x_4876_);
                    v___x_4878_ = v___x_4870_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4879_, 0, v___x_4876_);
                    v___x_4878_ = v_reuseFailAlloc_4879_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4878_;
            }
            7 => {
                if v_isShared_4884_ == 0 {
                    v___x_4886_ = v___x_4883_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4887_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
                    v___x_4886_ = v_reuseFailAlloc_4887_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4886_;
            }
            9 => {
                if v_isShared_4892_ == 0 {
                    v___x_4894_ = v___x_4891_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4895_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
                    v___x_4894_ = v_reuseFailAlloc_4895_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_4897_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_4898_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_4899_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_4900_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_4901_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4902_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_c_x27_4903_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_h_4904_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_x27_4905_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_fallback_4906_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_4907_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_4908_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_4909_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_4910_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_4911_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_4912_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_4913_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_4914_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_4915_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_4916_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_res_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4917_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(
            v_f_4897_,
            v_00_u03b1_4898_,
            v_c_4899_,
            v_inst_4900_,
            v_a_4901_,
            v_b_4902_,
            v_c_x27_4903_,
            v_h_4904_,
            v_inst_x27_4905_,
            v_fallback_4906_,
            v_a_4907_,
            v_a_4908_,
            v_a_4909_,
            v_a_4910_,
            v_a_4911_,
            v_a_4912_,
            v_a_4913_,
            v_a_4914_,
            v_a_4915_,
        );
    leanh::lean_dec(v_a_4915_);
    leanh::lean_dec_ref(v_a_4914_);
    leanh::lean_dec(v_a_4913_);
    leanh::lean_dec_ref(v_a_4912_);
    leanh::lean_dec(v_a_4911_);
    leanh::lean_dec_ref(v_a_4910_);
    leanh::lean_dec(v_a_4909_);
    leanh::lean_dec_ref(v_a_4908_);
    leanh::lean_dec(v_a_4907_);
    leanh::lean_dec_ref(v_f_4897_);
    return v_res_4917_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(
    mut v_f_4918_: *mut leanh::LeanObject,
    mut v_00_u03b1_4919_: *mut leanh::LeanObject,
    mut v_c_4920_: *mut leanh::LeanObject,
    mut v_inst_4921_: *mut leanh::LeanObject,
    mut v_a_4922_: *mut leanh::LeanObject,
    mut v_b_4923_: *mut leanh::LeanObject,
    mut v_fallback_4924_: *mut leanh::LeanObject,
    mut v_a_4925_: *mut leanh::LeanObject,
    mut v_a_4926_: *mut leanh::LeanObject,
    mut v_a_4927_: *mut leanh::LeanObject,
    mut v_a_4928_: *mut leanh::LeanObject,
    mut v_a_4929_: *mut leanh::LeanObject,
    mut v_a_4930_: *mut leanh::LeanObject,
    mut v_a_4931_: *mut leanh::LeanObject,
    mut v_a_4932_: *mut leanh::LeanObject,
    mut v_a_4933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4937_: u8 = 0;
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4941_: u8 = 0;
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4944_: u8 = 0;
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_unused_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4951_: u8 = 0;
    let mut v_contextDependent_4952_: u8 = 0;
    let mut v_e_x27_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4954_: u8 = 0;
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4958_: u8 = 0;
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4961_: u8 = 0;
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4966_: u8 = 0;
    let mut v_unused_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_4968_: u8 = 0;
    let mut v_contextDependent_4969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_4933_);
                leanh::lean_inc_ref(v_a_4932_);
                leanh::lean_inc(v_a_4931_);
                leanh::lean_inc_ref(v_a_4930_);
                leanh::lean_inc(v_a_4929_);
                leanh::lean_inc_ref(v_a_4928_);
                leanh::lean_inc(v_a_4927_);
                leanh::lean_inc_ref(v_a_4926_);
                leanh::lean_inc(v_a_4925_);
                leanh::lean_inc_ref(v_inst_4921_);
                v___x_4935_ = lean_sym_simp(
                    v_inst_4921_,
                    v_a_4925_,
                    v_a_4926_,
                    v_a_4927_,
                    v_a_4928_,
                    v_a_4929_,
                    v_a_4930_,
                    v_a_4931_,
                    v_a_4932_,
                    v_a_4933_,
                );
                if leanh::lean_obj_tag(v___x_4935_) == 0 {
                    v_a_4936_ = leanh::lean_ctor_get(v___x_4935_, 0);
                    leanh::lean_inc(v_a_4936_);
                    leanh::lean_dec_ref_known(v___x_4935_, 1);
                    if leanh::lean_obj_tag(v_a_4936_) == 0 {
                        v_contextDependent_4937_ =
                            leanh::lean_ctor_get_uint8(v_a_4936_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_4936_, 0);
                        leanh::lean_inc_ref(v_inst_4921_);
                        v___x_4938_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_4918_, v_00_u03b1_4919_, v_c_4920_, v_inst_4921_, v_a_4922_, v_b_4923_, v_inst_4921_, v_fallback_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
                        if leanh::lean_obj_tag(v___x_4938_) == 0 {
                            v_a_4939_ = leanh::lean_ctor_get(v___x_4938_, 0);
                            leanh::lean_inc(v_a_4939_);
                            if v_contextDependent_4937_ == 0 {
                                leanh::lean_dec(v_a_4939_);
                                return v___x_4938_;
                            } else {
                                if leanh::lean_obj_tag(v_a_4939_) == 0 {
                                    v_contextDependent_4951_ =
                                        leanh::lean_ctor_get_uint8(v_a_4939_, 1 as u32);
                                    v___y_4941_ = v_contextDependent_4951_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_contextDependent_4952_ = leanh::lean_ctor_get_uint8(
                                        v_a_4939_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_4941_ = v_contextDependent_4952_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_4938_;
                        }
                    } else {
                        v_e_x27_4953_ = leanh::lean_ctor_get(v_a_4936_, 0);
                        leanh::lean_inc_ref(v_e_x27_4953_);
                        v_contextDependent_4954_ = leanh::lean_ctor_get_uint8(
                            v_a_4936_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        leanh::lean_dec_ref_known(v_a_4936_, 2);
                        v___x_4955_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidable(v_f_4918_, v_00_u03b1_4919_, v_c_4920_, v_inst_4921_, v_a_4922_, v_b_4923_, v_e_x27_4953_, v_fallback_4924_, v_a_4925_, v_a_4926_, v_a_4927_, v_a_4928_, v_a_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
                        if leanh::lean_obj_tag(v___x_4955_) == 0 {
                            v_a_4956_ = leanh::lean_ctor_get(v___x_4955_, 0);
                            leanh::lean_inc(v_a_4956_);
                            if v_contextDependent_4954_ == 0 {
                                leanh::lean_dec(v_a_4956_);
                                return v___x_4955_;
                            } else {
                                if leanh::lean_obj_tag(v_a_4956_) == 0 {
                                    v_contextDependent_4968_ =
                                        leanh::lean_ctor_get_uint8(v_a_4956_, 1 as u32);
                                    v___y_4958_ = v_contextDependent_4968_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_contextDependent_4969_ = leanh::lean_ctor_get_uint8(
                                        v_a_4956_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_4958_ = v_contextDependent_4969_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_4955_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_4924_);
                    leanh::lean_dec_ref(v_b_4923_);
                    leanh::lean_dec_ref(v_a_4922_);
                    leanh::lean_dec_ref(v_inst_4921_);
                    leanh::lean_dec_ref(v_c_4920_);
                    leanh::lean_dec_ref(v_00_u03b1_4919_);
                    return v___x_4935_;
                }
            }
            1 => {
                if v___y_4941_ == 0 {
                    v_isSharedCheck_4949_ = (!leanh::lean_is_exclusive(v___x_4938_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v_unused_4950_ = leanh::lean_ctor_get(v___x_4938_, 0);
                        leanh::lean_dec(v_unused_4950_);
                        v___x_4943_ = v___x_4938_;
                        v_isShared_4944_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4938_);
                        v___x_4943_ = leanh::lean_box(0);
                        v_isShared_4944_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4939_);
                    return v___x_4938_;
                }
            }
            2 => {
                v___x_4945_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4939_);
                if v_isShared_4944_ == 0 {
                    leanh::lean_ctor_set(v___x_4943_, 0, v___x_4945_);
                    v___x_4947_ = v___x_4943_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4948_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4945_);
                    v___x_4947_ = v_reuseFailAlloc_4948_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4947_;
            }
            4 => {
                if v___y_4958_ == 0 {
                    v_isSharedCheck_4966_ = (!leanh::lean_is_exclusive(v___x_4955_)) as u8;
                    if v_isSharedCheck_4966_ == 0 {
                        v_unused_4967_ = leanh::lean_ctor_get(v___x_4955_, 0);
                        leanh::lean_dec(v_unused_4967_);
                        v___x_4960_ = v___x_4955_;
                        v_isShared_4961_ = v_isSharedCheck_4966_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4955_);
                        v___x_4960_ = leanh::lean_box(0);
                        v_isShared_4961_ = v_isSharedCheck_4966_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4956_);
                    return v___x_4955_;
                }
            }
            5 => {
                v___x_4962_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_4956_);
                if v_isShared_4961_ == 0 {
                    leanh::lean_ctor_set(v___x_4960_, 0, v___x_4962_);
                    v___x_4964_ = v___x_4960_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4965_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4965_, 0, v___x_4962_);
                    v___x_4964_ = v_reuseFailAlloc_4965_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_4970_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_4971_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_4972_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_4973_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_4974_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4975_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_fallback_4976_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_a_4977_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_a_4978_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_a_4979_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_4980_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_4981_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_4982_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_4983_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_4984_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_4985_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_4986_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4987_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v_f_4970_, v_00_u03b1_4971_, v_c_4972_, v_inst_4973_, v_a_4974_, v_b_4975_, v_fallback_4976_, v_a_4977_, v_a_4978_, v_a_4979_, v_a_4980_, v_a_4981_, v_a_4982_, v_a_4983_, v_a_4984_, v_a_4985_);
    leanh::lean_dec(v_a_4985_);
    leanh::lean_dec_ref(v_a_4984_);
    leanh::lean_dec(v_a_4983_);
    leanh::lean_dec_ref(v_a_4982_);
    leanh::lean_dec(v_a_4981_);
    leanh::lean_dec_ref(v_a_4980_);
    leanh::lean_dec(v_a_4979_);
    leanh::lean_dec_ref(v_a_4978_);
    leanh::lean_dec(v_a_4977_);
    leanh::lean_dec_ref(v_f_4970_);
    return v_res_4987_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(
    mut v_f_4988_: *mut leanh::LeanObject,
    mut v_00_u03b1_4989_: *mut leanh::LeanObject,
    mut v_c_4990_: *mut leanh::LeanObject,
    mut v_inst_4991_: *mut leanh::LeanObject,
    mut v_a_4992_: *mut leanh::LeanObject,
    mut v_b_4993_: *mut leanh::LeanObject,
    mut v_c_x27_4994_: *mut leanh::LeanObject,
    mut v_h_4995_: *mut leanh::LeanObject,
    mut v_inst_x27_4996_: *mut leanh::LeanObject,
    mut v_fallback_4997_: *mut leanh::LeanObject,
    mut v_a_4998_: *mut leanh::LeanObject,
    mut v_a_4999_: *mut leanh::LeanObject,
    mut v_a_5000_: *mut leanh::LeanObject,
    mut v_a_5001_: *mut leanh::LeanObject,
    mut v_a_5002_: *mut leanh::LeanObject,
    mut v_a_5003_: *mut leanh::LeanObject,
    mut v_a_5004_: *mut leanh::LeanObject,
    mut v_a_5005_: *mut leanh::LeanObject,
    mut v_a_5006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5010_: u8 = 0;
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5014_: u8 = 0;
    let mut v___x_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5017_: u8 = 0;
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5022_: u8 = 0;
    let mut v_unused_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5024_: u8 = 0;
    let mut v_contextDependent_5025_: u8 = 0;
    let mut v_e_x27_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5027_: u8 = 0;
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5031_: u8 = 0;
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5034_: u8 = 0;
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5039_: u8 = 0;
    let mut v_unused_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5041_: u8 = 0;
    let mut v_contextDependent_5042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_5006_);
                leanh::lean_inc_ref(v_a_5005_);
                leanh::lean_inc(v_a_5004_);
                leanh::lean_inc_ref(v_a_5003_);
                leanh::lean_inc(v_a_5002_);
                leanh::lean_inc_ref(v_a_5001_);
                leanh::lean_inc(v_a_5000_);
                leanh::lean_inc_ref(v_a_4999_);
                leanh::lean_inc(v_a_4998_);
                leanh::lean_inc_ref(v_inst_x27_4996_);
                v___x_5008_ = lean_sym_simp(
                    v_inst_x27_4996_,
                    v_a_4998_,
                    v_a_4999_,
                    v_a_5000_,
                    v_a_5001_,
                    v_a_5002_,
                    v_a_5003_,
                    v_a_5004_,
                    v_a_5005_,
                    v_a_5006_,
                );
                if leanh::lean_obj_tag(v___x_5008_) == 0 {
                    v_a_5009_ = leanh::lean_ctor_get(v___x_5008_, 0);
                    leanh::lean_inc(v_a_5009_);
                    leanh::lean_dec_ref_known(v___x_5008_, 1);
                    if leanh::lean_obj_tag(v_a_5009_) == 0 {
                        v_contextDependent_5010_ =
                            leanh::lean_ctor_get_uint8(v_a_5009_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_5009_, 0);
                        v___x_5011_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_4988_, v_00_u03b1_4989_, v_c_4990_, v_inst_4991_, v_a_4992_, v_b_4993_, v_c_x27_4994_, v_h_4995_, v_inst_x27_4996_, v_fallback_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_);
                        if leanh::lean_obj_tag(v___x_5011_) == 0 {
                            v_a_5012_ = leanh::lean_ctor_get(v___x_5011_, 0);
                            leanh::lean_inc(v_a_5012_);
                            if v_contextDependent_5010_ == 0 {
                                leanh::lean_dec(v_a_5012_);
                                return v___x_5011_;
                            } else {
                                if leanh::lean_obj_tag(v_a_5012_) == 0 {
                                    v_contextDependent_5024_ =
                                        leanh::lean_ctor_get_uint8(v_a_5012_, 1 as u32);
                                    v___y_5014_ = v_contextDependent_5024_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_contextDependent_5025_ = leanh::lean_ctor_get_uint8(
                                        v_a_5012_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_5014_ = v_contextDependent_5025_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_5011_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_x27_4996_);
                        v_e_x27_5026_ = leanh::lean_ctor_get(v_a_5009_, 0);
                        leanh::lean_inc_ref(v_e_x27_5026_);
                        v_contextDependent_5027_ = leanh::lean_ctor_get_uint8(
                            v_a_5009_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        leanh::lean_dec_ref_known(v_a_5009_, 2);
                        v___x_5028_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr(v_f_4988_, v_00_u03b1_4989_, v_c_4990_, v_inst_4991_, v_a_4992_, v_b_4993_, v_c_x27_4994_, v_h_4995_, v_e_x27_5026_, v_fallback_4997_, v_a_4998_, v_a_4999_, v_a_5000_, v_a_5001_, v_a_5002_, v_a_5003_, v_a_5004_, v_a_5005_, v_a_5006_);
                        if leanh::lean_obj_tag(v___x_5028_) == 0 {
                            v_a_5029_ = leanh::lean_ctor_get(v___x_5028_, 0);
                            leanh::lean_inc(v_a_5029_);
                            if v_contextDependent_5027_ == 0 {
                                leanh::lean_dec(v_a_5029_);
                                return v___x_5028_;
                            } else {
                                if leanh::lean_obj_tag(v_a_5029_) == 0 {
                                    v_contextDependent_5041_ =
                                        leanh::lean_ctor_get_uint8(v_a_5029_, 1 as u32);
                                    v___y_5031_ = v_contextDependent_5041_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_contextDependent_5042_ = leanh::lean_ctor_get_uint8(
                                        v_a_5029_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_5031_ = v_contextDependent_5042_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_5028_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_4997_);
                    leanh::lean_dec_ref(v_inst_x27_4996_);
                    leanh::lean_dec_ref(v_h_4995_);
                    leanh::lean_dec_ref(v_c_x27_4994_);
                    leanh::lean_dec_ref(v_b_4993_);
                    leanh::lean_dec_ref(v_a_4992_);
                    leanh::lean_dec_ref(v_inst_4991_);
                    leanh::lean_dec_ref(v_c_4990_);
                    leanh::lean_dec_ref(v_00_u03b1_4989_);
                    return v___x_5008_;
                }
            }
            1 => {
                if v___y_5014_ == 0 {
                    v_isSharedCheck_5022_ = (!leanh::lean_is_exclusive(v___x_5011_)) as u8;
                    if v_isSharedCheck_5022_ == 0 {
                        v_unused_5023_ = leanh::lean_ctor_get(v___x_5011_, 0);
                        leanh::lean_dec(v_unused_5023_);
                        v___x_5016_ = v___x_5011_;
                        v_isShared_5017_ = v_isSharedCheck_5022_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5011_);
                        v___x_5016_ = leanh::lean_box(0);
                        v_isShared_5017_ = v_isSharedCheck_5022_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5012_);
                    return v___x_5011_;
                }
            }
            2 => {
                v___x_5018_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_5012_);
                if v_isShared_5017_ == 0 {
                    leanh::lean_ctor_set(v___x_5016_, 0, v___x_5018_);
                    v___x_5020_ = v___x_5016_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5021_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5021_, 0, v___x_5018_);
                    v___x_5020_ = v_reuseFailAlloc_5021_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5020_;
            }
            4 => {
                if v___y_5031_ == 0 {
                    v_isSharedCheck_5039_ = (!leanh::lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5039_ == 0 {
                        v_unused_5040_ = leanh::lean_ctor_get(v___x_5028_, 0);
                        leanh::lean_dec(v_unused_5040_);
                        v___x_5033_ = v___x_5028_;
                        v_isShared_5034_ = v_isSharedCheck_5039_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5028_);
                        v___x_5033_ = leanh::lean_box(0);
                        v_isShared_5034_ = v_isSharedCheck_5039_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5029_);
                    return v___x_5028_;
                }
            }
            5 => {
                v___x_5035_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_5029_);
                if v_isShared_5034_ == 0 {
                    leanh::lean_ctor_set(v___x_5033_, 0, v___x_5035_);
                    v___x_5037_ = v___x_5033_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5038_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5038_, 0, v___x_5035_);
                    v___x_5037_ = v_reuseFailAlloc_5038_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_5043_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b1_5044_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_c_5045_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_inst_5046_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_a_5047_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_5048_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_c_x27_5049_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_h_5050_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_inst_x27_5051_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_fallback_5052_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_a_5053_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_a_5054_: *mut leanh::LeanObject = *_args.add(11);
    let mut v_a_5055_: *mut leanh::LeanObject = *_args.add(12);
    let mut v_a_5056_: *mut leanh::LeanObject = *_args.add(13);
    let mut v_a_5057_: *mut leanh::LeanObject = *_args.add(14);
    let mut v_a_5058_: *mut leanh::LeanObject = *_args.add(15);
    let mut v_a_5059_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_a_5060_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_a_5061_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_a_5062_: *mut leanh::LeanObject = *_args.add(19);
    let mut v_res_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr(v_f_5043_, v_00_u03b1_5044_, v_c_5045_, v_inst_5046_, v_a_5047_, v_b_5048_, v_c_x27_5049_, v_h_5050_, v_inst_x27_5051_, v_fallback_5052_, v_a_5053_, v_a_5054_, v_a_5055_, v_a_5056_, v_a_5057_, v_a_5058_, v_a_5059_, v_a_5060_, v_a_5061_);
    leanh::lean_dec(v_a_5061_);
    leanh::lean_dec_ref(v_a_5060_);
    leanh::lean_dec(v_a_5059_);
    leanh::lean_dec_ref(v_a_5058_);
    leanh::lean_dec(v_a_5057_);
    leanh::lean_dec_ref(v_a_5056_);
    leanh::lean_dec(v_a_5055_);
    leanh::lean_dec_ref(v_a_5054_);
    leanh::lean_dec(v_a_5053_);
    leanh::lean_dec_ref(v_f_5043_);
    return v_res_5063_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5067_ = leanh::lean_unsigned_to_nat(0);
    v___x_5068_ = l_Lean_mkBVar(v___x_5067_);
    return v___x_5068_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(
    mut v_proof_5074_: *mut leanh::LeanObject,
    mut v___x_5075_: *mut leanh::LeanObject,
    mut v_arg_5076_: *mut leanh::LeanObject,
    mut v_e_x27_5077_: *mut leanh::LeanObject,
    mut v_arg_5078_: *mut leanh::LeanObject,
    mut v_a_5079_: u8,
    mut v_arg_5080_: *mut leanh::LeanObject,
    mut v___x_5081_: *mut leanh::LeanObject,
    mut v___x_5082_: *mut leanh::LeanObject,
    mut v_e_5083_: *mut leanh::LeanObject,
    mut v___x_5084_: u8,
    mut v_contextDependent_5085_: u8,
    mut v___y_5086_: *mut leanh::LeanObject,
    mut v___y_5087_: *mut leanh::LeanObject,
    mut v___y_5088_: *mut leanh::LeanObject,
    mut v___y_5089_: *mut leanh::LeanObject,
    mut v___y_5090_: *mut leanh::LeanObject,
    mut v___y_5091_: *mut leanh::LeanObject,
    mut v___y_5092_: *mut leanh::LeanObject,
    mut v___y_5093_: *mut leanh::LeanObject,
    mut v___y_5094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: u8 = 0;
    let mut v___x_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5124_: u8 = 0;
    let mut v___x_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5132_: u8 = 0;
    let mut v_a_5133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5136_: u8 = 0;
    let mut v___x_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5140_: u8 = 0;
    let mut v_a_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5144_: u8 = 0;
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5148_: u8 = 0;
    let mut v_a_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5152_: u8 = 0;
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5156_: u8 = 0;
    let mut v_a_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5160_: u8 = 0;
    let mut v___x_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5164_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5096_ = l_Lean_Meta_Sym_shareCommon___redArg(v_proof_5074_, v___y_5090_);
                if leanh::lean_obj_tag(v___x_5096_) == 0 {
                    v_a_5097_ = leanh::lean_ctor_get(v___x_5096_, 0);
                    leanh::lean_inc_n(v_a_5097_, 2);
                    leanh::lean_dec_ref_known(v___x_5096_, 1);
                    v___x_5098_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__1;
                    v___x_5099_ = 0;
                    v___x_5100_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__2;
                    leanh::lean_inc(v___x_5075_);
                    v___x_5101_ = l_Lean_mkConst(v___x_5100_, v___x_5075_);
                    v___x_5102_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__2);
                    leanh::lean_inc_ref_n(v_e_x27_5077_, 2);
                    leanh::lean_inc_ref(v_arg_5076_);
                    v___x_5103_ = l_Lean_mkApp4(
                        v___x_5101_,
                        v_arg_5076_,
                        v_e_x27_5077_,
                        v_a_5097_,
                        v___x_5102_,
                    );
                    v___x_5104_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5105_ = lean_mk_empty_array_with_capacity(v___x_5104_);
                    leanh::lean_inc_ref(v___x_5105_);
                    v___x_5106_ = lean_array_push(v___x_5105_, v___x_5103_);
                    v___x_5107_ =
                        l_Lean_Expr_betaRev(v_arg_5078_, v___x_5106_, v_a_5079_, v_a_5079_);
                    leanh::lean_dec_ref(v___x_5106_);
                    v___x_5108_ =
                        l_Lean_mkLambda(v___x_5098_, v___x_5099_, v_e_x27_5077_, v___x_5107_);
                    v___x_5109_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_5108_, v___y_5090_);
                    if leanh::lean_obj_tag(v___x_5109_) == 0 {
                        v_a_5110_ = leanh::lean_ctor_get(v___x_5109_, 0);
                        leanh::lean_inc(v_a_5110_);
                        leanh::lean_dec_ref_known(v___x_5109_, 1);
                        leanh::lean_inc_ref_n(v_e_x27_5077_, 2);
                        v___x_5111_ = l_Lean_mkNot(v_e_x27_5077_);
                        v___x_5112_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDIteDecidableCongr___closed__7;
                        v___x_5113_ = l_Lean_mkConst(v___x_5112_, v___x_5075_);
                        leanh::lean_inc(v_a_5097_);
                        v___x_5114_ = l_Lean_mkApp4(
                            v___x_5113_,
                            v_arg_5076_,
                            v_e_x27_5077_,
                            v_a_5097_,
                            v___x_5102_,
                        );
                        v___x_5115_ = lean_array_push(v___x_5105_, v___x_5114_);
                        v___x_5116_ =
                            l_Lean_Expr_betaRev(v_arg_5080_, v___x_5115_, v_a_5079_, v_a_5079_);
                        leanh::lean_dec_ref(v___x_5115_);
                        v___x_5117_ =
                            l_Lean_mkLambda(v___x_5098_, v___x_5099_, v___x_5111_, v___x_5116_);
                        v___x_5118_ =
                            l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_5117_, v___y_5090_);
                        if leanh::lean_obj_tag(v___x_5118_) == 0 {
                            v_a_5119_ = leanh::lean_ctor_get(v___x_5118_, 0);
                            leanh::lean_inc(v_a_5119_);
                            leanh::lean_dec_ref_known(v___x_5118_, 1);
                            leanh::lean_inc_ref(v___x_5082_);
                            leanh::lean_inc_ref(v_e_x27_5077_);
                            v___x_5120_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0(v___x_5081_, v_e_x27_5077_, v___x_5082_, v_a_5110_, v_a_5119_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
                            if leanh::lean_obj_tag(v___x_5120_) == 0 {
                                v_a_5121_ = leanh::lean_ctor_get(v___x_5120_, 0);
                                v_isSharedCheck_5132_ =
                                    (!leanh::lean_is_exclusive(v___x_5120_)) as u8;
                                if v_isSharedCheck_5132_ == 0 {
                                    v___x_5123_ = v___x_5120_;
                                    v_isShared_5124_ = v_isSharedCheck_5132_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5121_);
                                    leanh::lean_dec(v___x_5120_);
                                    v___x_5123_ = leanh::lean_box(0);
                                    v_isShared_5124_ = v_isSharedCheck_5132_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5097_);
                                leanh::lean_dec_ref(v_e_5083_);
                                leanh::lean_dec_ref(v___x_5082_);
                                leanh::lean_dec_ref(v_e_x27_5077_);
                                v_a_5133_ = leanh::lean_ctor_get(v___x_5120_, 0);
                                v_isSharedCheck_5140_ =
                                    (!leanh::lean_is_exclusive(v___x_5120_)) as u8;
                                if v_isSharedCheck_5140_ == 0 {
                                    v___x_5135_ = v___x_5120_;
                                    v_isShared_5136_ = v_isSharedCheck_5140_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5133_);
                                    leanh::lean_dec(v___x_5120_);
                                    v___x_5135_ = leanh::lean_box(0);
                                    v_isShared_5136_ = v_isSharedCheck_5140_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_5110_);
                            leanh::lean_dec(v_a_5097_);
                            leanh::lean_dec_ref(v_e_5083_);
                            leanh::lean_dec_ref(v___x_5082_);
                            leanh::lean_dec_ref(v___x_5081_);
                            leanh::lean_dec_ref(v_e_x27_5077_);
                            v_a_5141_ = leanh::lean_ctor_get(v___x_5118_, 0);
                            v_isSharedCheck_5148_ =
                                (!leanh::lean_is_exclusive(v___x_5118_)) as u8;
                            if v_isSharedCheck_5148_ == 0 {
                                v___x_5143_ = v___x_5118_;
                                v_isShared_5144_ = v_isSharedCheck_5148_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5141_);
                                leanh::lean_dec(v___x_5118_);
                                v___x_5143_ = leanh::lean_box(0);
                                v_isShared_5144_ = v_isSharedCheck_5148_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5105_);
                        leanh::lean_dec(v_a_5097_);
                        leanh::lean_dec_ref(v_e_5083_);
                        leanh::lean_dec_ref(v___x_5082_);
                        leanh::lean_dec_ref(v___x_5081_);
                        leanh::lean_dec_ref(v_arg_5080_);
                        leanh::lean_dec_ref(v_e_x27_5077_);
                        leanh::lean_dec_ref(v_arg_5076_);
                        leanh::lean_dec(v___x_5075_);
                        v_a_5149_ = leanh::lean_ctor_get(v___x_5109_, 0);
                        v_isSharedCheck_5156_ =
                            (!leanh::lean_is_exclusive(v___x_5109_)) as u8;
                        if v_isSharedCheck_5156_ == 0 {
                            v___x_5151_ = v___x_5109_;
                            v_isShared_5152_ = v_isSharedCheck_5156_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5149_);
                            leanh::lean_dec(v___x_5109_);
                            v___x_5151_ = leanh::lean_box(0);
                            v_isShared_5152_ = v_isSharedCheck_5156_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_5083_);
                    leanh::lean_dec_ref(v___x_5082_);
                    leanh::lean_dec_ref(v___x_5081_);
                    leanh::lean_dec_ref(v_arg_5080_);
                    leanh::lean_dec_ref(v_arg_5078_);
                    leanh::lean_dec_ref(v_e_x27_5077_);
                    leanh::lean_dec_ref(v_arg_5076_);
                    leanh::lean_dec(v___x_5075_);
                    v_a_5157_ = leanh::lean_ctor_get(v___x_5096_, 0);
                    v_isSharedCheck_5164_ = (!leanh::lean_is_exclusive(v___x_5096_)) as u8;
                    if v_isSharedCheck_5164_ == 0 {
                        v___x_5159_ = v___x_5096_;
                        v_isShared_5160_ = v_isSharedCheck_5164_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5157_);
                        leanh::lean_dec(v___x_5096_);
                        v___x_5159_ = leanh::lean_box(0);
                        v_isShared_5160_ = v_isSharedCheck_5164_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5125_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___closed__4;
                v___x_5126_ = l_Lean_Expr_replaceFn(v_e_5083_, v___x_5125_);
                v___x_5127_ = l_Lean_mkApp3(v___x_5126_, v_e_x27_5077_, v___x_5082_, v_a_5097_);
                v___x_5128_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5128_, 0, v_a_5121_);
                leanh::lean_ctor_set(v___x_5128_, 1, v___x_5127_);
                leanh::lean_ctor_set_uint8(
                    v___x_5128_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5084_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5128_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_5085_,
                );
                if v_isShared_5124_ == 0 {
                    leanh::lean_ctor_set(v___x_5123_, 0, v___x_5128_);
                    v___x_5130_ = v___x_5123_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5131_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5131_, 0, v___x_5128_);
                    v___x_5130_ = v_reuseFailAlloc_5131_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5130_;
            }
            3 => {
                if v_isShared_5136_ == 0 {
                    v___x_5138_ = v___x_5135_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5139_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
                    v___x_5138_ = v_reuseFailAlloc_5139_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5138_;
            }
            5 => {
                if v_isShared_5144_ == 0 {
                    v___x_5146_ = v___x_5143_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5147_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5147_, 0, v_a_5141_);
                    v___x_5146_ = v_reuseFailAlloc_5147_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5146_;
            }
            7 => {
                if v_isShared_5152_ == 0 {
                    v___x_5154_ = v___x_5151_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5155_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5155_, 0, v_a_5149_);
                    v___x_5154_ = v_reuseFailAlloc_5155_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5154_;
            }
            9 => {
                if v_isShared_5160_ == 0 {
                    v___x_5162_ = v___x_5159_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5163_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v_a_5157_);
                    v___x_5162_ = v_reuseFailAlloc_5163_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5162_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_proof_5165_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_5166_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_arg_5167_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_e_x27_5168_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_arg_5169_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_a_5170_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_arg_5171_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___x_5172_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___x_5173_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_e_5174_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___x_5175_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_contextDependent_5176_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5177_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5178_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5179_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5180_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5181_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5182_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_5183_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_5184_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_5185_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___y_5186_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_a_32592__boxed_5187_: u8 = 0;
    let mut v___x_32596__boxed_5188_: u8 = 0;
    let mut v_contextDependent_32597__boxed_5189_: u8 = 0;
    let mut v_res_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_32592__boxed_5187_ = (leanh::lean_unbox(v_a_5170_) as u8);
    v___x_32596__boxed_5188_ = (leanh::lean_unbox(v___x_5175_) as u8);
    v_contextDependent_32597__boxed_5189_ =
        (leanh::lean_unbox(v_contextDependent_5176_) as u8);
    v_res_5190_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1(
            v_proof_5165_,
            v___x_5166_,
            v_arg_5167_,
            v_e_x27_5168_,
            v_arg_5169_,
            v_a_32592__boxed_5187_,
            v_arg_5171_,
            v___x_5172_,
            v___x_5173_,
            v_e_5174_,
            v___x_32596__boxed_5188_,
            v_contextDependent_32597__boxed_5189_,
            v___y_5177_,
            v___y_5178_,
            v___y_5179_,
            v___y_5180_,
            v___y_5181_,
            v___y_5182_,
            v___y_5183_,
            v___y_5184_,
            v___y_5185_,
        );
    leanh::lean_dec(v___y_5185_);
    leanh::lean_dec_ref(v___y_5184_);
    leanh::lean_dec(v___y_5183_);
    leanh::lean_dec_ref(v___y_5182_);
    leanh::lean_dec(v___y_5181_);
    leanh::lean_dec_ref(v___y_5180_);
    leanh::lean_dec(v___y_5179_);
    leanh::lean_dec_ref(v___y_5178_);
    leanh::lean_dec(v___y_5177_);
    return v_res_5190_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5197_ = leanh::lean_box(0);
    v___x_5198_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__3;
    v___x_5199_ = l_Lean_mkConst(v___x_5198_, v___x_5197_);
    return v___x_5199_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5200_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__4);
    v___x_5201_ = leanh::lean_unsigned_to_nat(1);
    v___x_5202_ = lean_mk_empty_array_with_capacity(v___x_5201_);
    v___x_5203_ = lean_array_push(v___x_5202_, v___x_5200_);
    return v___x_5203_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5211_ = leanh::lean_box(0);
    v___x_5212_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__9;
    v___x_5213_ = l_Lean_mkConst(v___x_5212_, v___x_5211_);
    return v___x_5213_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__10);
    v___x_5215_ = leanh::lean_unsigned_to_nat(1);
    v___x_5216_ = lean_mk_empty_array_with_capacity(v___x_5215_);
    v___x_5217_ = lean_array_push(v___x_5216_, v___x_5214_);
    return v___x_5217_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(
    mut v___x_5226_: u8,
    mut v_e_5227_: *mut leanh::LeanObject,
    mut v___y_5228_: *mut leanh::LeanObject,
    mut v___y_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
    mut v___y_5231_: *mut leanh::LeanObject,
    mut v___y_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: u8 = 0;
    let mut v_arg_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: u8 = 0;
    let mut v_arg_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: u8 = 0;
    let mut v_arg_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: u8 = 0;
    let mut v_arg_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: u8 = 0;
    let mut v_arg_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: u8 = 0;
    let mut v___x_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5261_: u8 = 0;
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: u8 = 0;
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: u8 = 0;
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: u8 = 0;
    let mut v___x_5273_: u8 = 0;
    let mut v___x_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: u8 = 0;
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5289_: u8 = 0;
    let mut v_a_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v___x_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5297_: u8 = 0;
    let mut v_a_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5321_: u8 = 0;
    let mut v_a_5322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5325_: u8 = 0;
    let mut v___x_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5329_: u8 = 0;
    let mut v_a_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5337_: u8 = 0;
    let mut v_e_x27_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5340_: u8 = 0;
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5343_: u8 = 0;
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: u8 = 0;
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: u8 = 0;
    let mut v___x_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5367_: u8 = 0;
    let mut v___x_5368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5373_: u8 = 0;
    let mut v___x_5374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: u8 = 0;
    let mut v___x_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5384_: u8 = 0;
    let mut v_a_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5388_: u8 = 0;
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5392_: u8 = 0;
    let mut v_a_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut v_a_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5408_: u8 = 0;
    let mut v___x_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5420_: u8 = 0;
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5430_: u8 = 0;
    let mut v_a_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5434_: u8 = 0;
    let mut v___x_5436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5438_: u8 = 0;
    let mut v_a_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5442_: u8 = 0;
    let mut v___x_5444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5446_: u8 = 0;
    let mut v_a_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut v_isSharedCheck_5455_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_5227_);
                v___x_5241_ = l_Lean_Expr_cleanupAnnotations(v_e_5227_);
                v___x_5242_ = l_Lean_Expr_isApp(v___x_5241_);
                if v___x_5242_ == 0 {
                    leanh::lean_dec_ref(v___x_5241_);
                    leanh::lean_dec_ref(v_e_5227_);
                    state = 1;
                    continue;
                } else {
                    v_arg_5243_ = leanh::lean_ctor_get(v___x_5241_, 1);
                    leanh::lean_inc_ref(v_arg_5243_);
                    v___x_5244_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5241_);
                    v___x_5245_ = l_Lean_Expr_isApp(v___x_5244_);
                    if v___x_5245_ == 0 {
                        leanh::lean_dec_ref(v___x_5244_);
                        leanh::lean_dec_ref(v_arg_5243_);
                        leanh::lean_dec_ref(v_e_5227_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_5246_ = leanh::lean_ctor_get(v___x_5244_, 1);
                        leanh::lean_inc_ref(v_arg_5246_);
                        v___x_5247_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5244_);
                        v___x_5248_ = l_Lean_Expr_isApp(v___x_5247_);
                        if v___x_5248_ == 0 {
                            leanh::lean_dec_ref(v___x_5247_);
                            leanh::lean_dec_ref(v_arg_5246_);
                            leanh::lean_dec_ref(v_arg_5243_);
                            leanh::lean_dec_ref(v_e_5227_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_5249_ = leanh::lean_ctor_get(v___x_5247_, 1);
                            leanh::lean_inc_ref(v_arg_5249_);
                            v___x_5250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5247_);
                            v___x_5251_ = l_Lean_Expr_isApp(v___x_5250_);
                            if v___x_5251_ == 0 {
                                leanh::lean_dec_ref(v___x_5250_);
                                leanh::lean_dec_ref(v_arg_5249_);
                                leanh::lean_dec_ref(v_arg_5246_);
                                leanh::lean_dec_ref(v_arg_5243_);
                                leanh::lean_dec_ref(v_e_5227_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_5252_ = leanh::lean_ctor_get(v___x_5250_, 1);
                                leanh::lean_inc_ref(v_arg_5252_);
                                v___x_5253_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5250_);
                                v___x_5254_ = l_Lean_Expr_isApp(v___x_5253_);
                                if v___x_5254_ == 0 {
                                    leanh::lean_dec_ref(v___x_5253_);
                                    leanh::lean_dec_ref(v_arg_5252_);
                                    leanh::lean_dec_ref(v_arg_5249_);
                                    leanh::lean_dec_ref(v_arg_5246_);
                                    leanh::lean_dec_ref(v_arg_5243_);
                                    leanh::lean_dec_ref(v_e_5227_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_arg_5255_ = leanh::lean_ctor_get(v___x_5253_, 1);
                                    leanh::lean_inc_ref(v_arg_5255_);
                                    v___x_5256_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5253_);
                                    v___x_5257_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__1;
                                    v___x_5258_ = l_Lean_Expr_isConstOf(v___x_5256_, v___x_5257_);
                                    if v___x_5258_ == 0 {
                                        leanh::lean_dec_ref(v___x_5256_);
                                        leanh::lean_dec_ref(v_arg_5255_);
                                        leanh::lean_dec_ref(v_arg_5252_);
                                        leanh::lean_dec_ref(v_arg_5249_);
                                        leanh::lean_dec_ref(v_arg_5246_);
                                        leanh::lean_dec_ref(v_arg_5243_);
                                        leanh::lean_dec_ref(v_e_5227_);
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v___y_5236_);
                                        leanh::lean_inc_ref(v___y_5235_);
                                        leanh::lean_inc(v___y_5234_);
                                        leanh::lean_inc_ref(v___y_5233_);
                                        leanh::lean_inc(v___y_5232_);
                                        leanh::lean_inc_ref(v___y_5231_);
                                        leanh::lean_inc(v___y_5230_);
                                        leanh::lean_inc_ref(v___y_5229_);
                                        leanh::lean_inc(v___y_5228_);
                                        leanh::lean_inc_ref(v_arg_5252_);
                                        v___x_5259_ = lean_sym_simp(
                                            v_arg_5252_,
                                            v___y_5228_,
                                            v___y_5229_,
                                            v___y_5230_,
                                            v___y_5231_,
                                            v___y_5232_,
                                            v___y_5233_,
                                            v___y_5234_,
                                            v___y_5235_,
                                            v___y_5236_,
                                        );
                                        if leanh::lean_obj_tag(v___x_5259_) == 0 {
                                            v_a_5260_ = leanh::lean_ctor_get(v___x_5259_, 0);
                                            leanh::lean_inc(v_a_5260_);
                                            leanh::lean_dec_ref_known(v___x_5259_, 1);
                                            if leanh::lean_obj_tag(v_a_5260_) == 0 {
                                                leanh::lean_dec_ref(v_e_5227_);
                                                v_contextDependent_5261_ =
                                                    leanh::lean_ctor_get_uint8(
                                                        v_a_5260_, 1 as u32,
                                                    );
                                                leanh::lean_dec_ref_known(v_a_5260_, 0);
                                                v___x_5262_ = l_Lean_Meta_Sym_isTrueExpr___redArg(
                                                    v_arg_5252_,
                                                    v___y_5231_,
                                                );
                                                if leanh::lean_obj_tag(v___x_5262_) == 0 {
                                                    v_a_5263_ =
                                                        leanh::lean_ctor_get(v___x_5262_, 0);
                                                    leanh::lean_inc(v_a_5263_);
                                                    leanh::lean_dec_ref_known(
                                                        v___x_5262_,
                                                        1,
                                                    );
                                                    v___x_5264_ =
                                                        (leanh::lean_unbox(v_a_5263_) as u8);
                                                    if v___x_5264_ == 0 {
                                                        v___x_5265_ =
                                                            l_Lean_Meta_Sym_isFalseExpr___redArg(
                                                                v_arg_5252_,
                                                                v___y_5231_,
                                                            );
                                                        if leanh::lean_obj_tag(v___x_5265_)
                                                            == 0
                                                        {
                                                            v_a_5266_ = leanh::lean_ctor_get(
                                                                v___x_5265_,
                                                                0,
                                                            );
                                                            leanh::lean_inc(v_a_5266_);
                                                            leanh::lean_dec_ref_known(
                                                                v___x_5265_,
                                                                1,
                                                            );
                                                            v___x_5267_ = (leanh::lean_unbox(
                                                                v_a_5266_,
                                                            )
                                                                as u8);
                                                            leanh::lean_dec(v_a_5266_);
                                                            if v___x_5267_ == 0 {
                                                                leanh::lean_dec(v_a_5263_);
                                                                v___x_5268_ = l_Lean_Meta_Sym_Simp_mkRflResult(v___x_5258_, v_contextDependent_5261_);
                                                                v___f_5269_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                                                                leanh::lean_closure_set(
                                                                    v___f_5269_,
                                                                    0,
                                                                    v___x_5268_,
                                                                );
                                                                v___x_5270_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_5256_, v_arg_5255_, v_arg_5252_, v_arg_5249_, v_arg_5246_, v_arg_5243_, v___f_5269_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
                                                                leanh::lean_dec_ref(
                                                                    v___x_5256_,
                                                                );
                                                                return v___x_5270_;
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v_arg_5252_,
                                                                );
                                                                leanh::lean_dec_ref(
                                                                    v_arg_5249_,
                                                                );
                                                                v___x_5271_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__5);
                                                                v___x_5272_ =
                                                                    (leanh::lean_unbox(
                                                                        v_a_5263_,
                                                                    )
                                                                        as u8);
                                                                v___x_5273_ =
                                                                    (leanh::lean_unbox(
                                                                        v_a_5263_,
                                                                    )
                                                                        as u8);
                                                                leanh::lean_inc_ref(
                                                                    v_arg_5243_,
                                                                );
                                                                v___x_5274_ = l_Lean_Expr_betaRev(
                                                                    v_arg_5243_,
                                                                    v___x_5271_,
                                                                    v___x_5272_,
                                                                    v___x_5273_,
                                                                );
                                                                v___x_5275_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_5274_, v___y_5232_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_5275_,
                                                                ) == 0
                                                                {
                                                                    v_a_5276_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_5275_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_5289_ = (!leanh::lean_is_exclusive(v___x_5275_)) as u8;
                                                                    if v_isSharedCheck_5289_ == 0 {
                                                                        v___x_5278_ = v___x_5275_;
                                                                        v_isShared_5279_ =
                                                                            v_isSharedCheck_5289_;
                                                                        state = 2;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_5276_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_5275_,
                                                                        );
                                                                        v___x_5278_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_5279_ =
                                                                            v_isSharedCheck_5289_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec(
                                                                        v_a_5263_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v___x_5256_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_5255_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_5246_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_5243_,
                                                                    );
                                                                    v_a_5290_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_5275_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_5297_ = (!leanh::lean_is_exclusive(v___x_5275_)) as u8;
                                                                    if v_isSharedCheck_5297_ == 0 {
                                                                        v___x_5292_ = v___x_5275_;
                                                                        v_isShared_5293_ =
                                                                            v_isSharedCheck_5297_;
                                                                        state = 4;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_5290_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_5275_,
                                                                        );
                                                                        v___x_5292_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_5293_ =
                                                                            v_isSharedCheck_5297_;
                                                                        state = 4;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            leanh::lean_dec(v_a_5263_);
                                                            leanh::lean_dec_ref(v___x_5256_);
                                                            leanh::lean_dec_ref(v_arg_5255_);
                                                            leanh::lean_dec_ref(v_arg_5252_);
                                                            leanh::lean_dec_ref(v_arg_5249_);
                                                            leanh::lean_dec_ref(v_arg_5246_);
                                                            leanh::lean_dec_ref(v_arg_5243_);
                                                            v_a_5298_ = leanh::lean_ctor_get(
                                                                v___x_5265_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5305_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_5265_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5305_ == 0 {
                                                                v___x_5300_ = v___x_5265_;
                                                                v_isShared_5301_ =
                                                                    v_isSharedCheck_5305_;
                                                                state = 6;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_5298_);
                                                                leanh::lean_dec(v___x_5265_);
                                                                v___x_5300_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_5301_ =
                                                                    v_isSharedCheck_5305_;
                                                                state = 6;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_a_5263_);
                                                        leanh::lean_dec_ref(v_arg_5252_);
                                                        leanh::lean_dec_ref(v_arg_5249_);
                                                        v___x_5306_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__11);
                                                        leanh::lean_inc_ref(v_arg_5246_);
                                                        v___x_5307_ = l_Lean_Expr_betaRev(
                                                            v_arg_5246_,
                                                            v___x_5306_,
                                                            v___x_5226_,
                                                            v___x_5226_,
                                                        );
                                                        v___x_5308_ =
                                                            l_Lean_Meta_Sym_shareCommonInc___redArg(
                                                                v___x_5307_,
                                                                v___y_5232_,
                                                            );
                                                        if leanh::lean_obj_tag(v___x_5308_)
                                                            == 0
                                                        {
                                                            v_a_5309_ = leanh::lean_ctor_get(
                                                                v___x_5308_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5321_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_5308_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5321_ == 0 {
                                                                v___x_5311_ = v___x_5308_;
                                                                v_isShared_5312_ =
                                                                    v_isSharedCheck_5321_;
                                                                state = 8;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_5309_);
                                                                leanh::lean_dec(v___x_5308_);
                                                                v___x_5311_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_5312_ =
                                                                    v_isSharedCheck_5321_;
                                                                state = 8;
                                                                continue;
                                                            }
                                                        } else {
                                                            leanh::lean_dec_ref(v___x_5256_);
                                                            leanh::lean_dec_ref(v_arg_5255_);
                                                            leanh::lean_dec_ref(v_arg_5246_);
                                                            leanh::lean_dec_ref(v_arg_5243_);
                                                            v_a_5322_ = leanh::lean_ctor_get(
                                                                v___x_5308_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_5329_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_5308_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_5329_ == 0 {
                                                                v___x_5324_ = v___x_5308_;
                                                                v_isShared_5325_ =
                                                                    v_isSharedCheck_5329_;
                                                                state = 10;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_5322_);
                                                                leanh::lean_dec(v___x_5308_);
                                                                v___x_5324_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_5325_ =
                                                                    v_isSharedCheck_5329_;
                                                                state = 10;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v___x_5256_);
                                                    leanh::lean_dec_ref(v_arg_5255_);
                                                    leanh::lean_dec_ref(v_arg_5252_);
                                                    leanh::lean_dec_ref(v_arg_5249_);
                                                    leanh::lean_dec_ref(v_arg_5246_);
                                                    leanh::lean_dec_ref(v_arg_5243_);
                                                    v_a_5330_ =
                                                        leanh::lean_ctor_get(v___x_5262_, 0);
                                                    v_isSharedCheck_5337_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_5262_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5337_ == 0 {
                                                        v___x_5332_ = v___x_5262_;
                                                        v_isShared_5333_ = v_isSharedCheck_5337_;
                                                        state = 12;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_5330_);
                                                        leanh::lean_dec(v___x_5262_);
                                                        v___x_5332_ = leanh::lean_box(0);
                                                        v_isShared_5333_ = v_isSharedCheck_5337_;
                                                        state = 12;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v_e_x27_5338_ =
                                                    leanh::lean_ctor_get(v_a_5260_, 0);
                                                v_proof_5339_ =
                                                    leanh::lean_ctor_get(v_a_5260_, 1);
                                                v_contextDependent_5340_ =
                                                    leanh::lean_ctor_get_uint8(
                                                        v_a_5260_,
                                                        (core::mem::size_of::<
                                                            *mut leanh::LeanObject,
                                                        >(
                                                        ) * 2
                                                            + 1)
                                                            as u32,
                                                    );
                                                v_isSharedCheck_5455_ =
                                                    (!leanh::lean_is_exclusive(v_a_5260_))
                                                        as u8;
                                                if v_isSharedCheck_5455_ == 0 {
                                                    v___x_5342_ = v_a_5260_;
                                                    v_isShared_5343_ = v_isSharedCheck_5455_;
                                                    state = 14;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_proof_5339_);
                                                    leanh::lean_inc(v_e_x27_5338_);
                                                    leanh::lean_dec(v_a_5260_);
                                                    v___x_5342_ = leanh::lean_box(0);
                                                    v_isShared_5343_ = v_isSharedCheck_5455_;
                                                    state = 14;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_5256_);
                                            leanh::lean_dec_ref(v_arg_5255_);
                                            leanh::lean_dec_ref(v_arg_5252_);
                                            leanh::lean_dec_ref(v_arg_5249_);
                                            leanh::lean_dec_ref(v_arg_5246_);
                                            leanh::lean_dec_ref(v_arg_5243_);
                                            leanh::lean_dec_ref(v_e_5227_);
                                            return v___x_5259_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5239_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                leanh::lean_ctor_set_uint8(v___x_5239_, 0 as u32, v___x_5226_);
                leanh::lean_ctor_set_uint8(v___x_5239_, 1 as u32, v___x_5226_);
                v___x_5240_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5240_, 0, v___x_5239_);
                return v___x_5240_;
            }
            2 => {
                v___x_5280_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__6;
                v___x_5281_ = l_Lean_Expr_constLevels_x21(v___x_5256_);
                leanh::lean_dec_ref(v___x_5256_);
                v___x_5282_ = l_Lean_mkConst(v___x_5280_, v___x_5281_);
                v___x_5283_ = l_Lean_mkApp3(v___x_5282_, v_arg_5255_, v_arg_5246_, v_arg_5243_);
                v___x_5284_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5284_, 0, v_a_5276_);
                leanh::lean_ctor_set(v___x_5284_, 1, v___x_5283_);
                v___x_5285_ = (leanh::lean_unbox(v_a_5263_) as u8);
                leanh::lean_dec(v_a_5263_);
                leanh::lean_ctor_set_uint8(
                    v___x_5284_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5285_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5284_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_5261_,
                );
                if v_isShared_5279_ == 0 {
                    leanh::lean_ctor_set(v___x_5278_, 0, v___x_5284_);
                    v___x_5287_ = v___x_5278_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5288_, 0, v___x_5284_);
                    v___x_5287_ = v_reuseFailAlloc_5288_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5287_;
            }
            4 => {
                if v_isShared_5293_ == 0 {
                    v___x_5295_ = v___x_5292_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5296_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
                    v___x_5295_ = v_reuseFailAlloc_5296_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5295_;
            }
            6 => {
                if v_isShared_5301_ == 0 {
                    v___x_5303_ = v___x_5300_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
                    v___x_5303_ = v_reuseFailAlloc_5304_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5303_;
            }
            8 => {
                v___x_5313_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__12;
                v___x_5314_ = l_Lean_Expr_constLevels_x21(v___x_5256_);
                leanh::lean_dec_ref(v___x_5256_);
                v___x_5315_ = l_Lean_mkConst(v___x_5313_, v___x_5314_);
                v___x_5316_ = l_Lean_mkApp3(v___x_5315_, v_arg_5255_, v_arg_5246_, v_arg_5243_);
                v___x_5317_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5317_, 0, v_a_5309_);
                leanh::lean_ctor_set(v___x_5317_, 1, v___x_5316_);
                leanh::lean_ctor_set_uint8(
                    v___x_5317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5226_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5317_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_5261_,
                );
                if v_isShared_5312_ == 0 {
                    leanh::lean_ctor_set(v___x_5311_, 0, v___x_5317_);
                    v___x_5319_ = v___x_5311_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5320_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5320_, 0, v___x_5317_);
                    v___x_5319_ = v_reuseFailAlloc_5320_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5319_;
            }
            10 => {
                if v_isShared_5325_ == 0 {
                    v___x_5327_ = v___x_5324_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
                    v___x_5327_ = v_reuseFailAlloc_5328_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5327_;
            }
            12 => {
                if v_isShared_5333_ == 0 {
                    v___x_5335_ = v___x_5332_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5336_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
                    v___x_5335_ = v_reuseFailAlloc_5336_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5335_;
            }
            14 => {
                v___x_5344_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_5338_, v___y_5231_);
                if leanh::lean_obj_tag(v___x_5344_) == 0 {
                    v_a_5345_ = leanh::lean_ctor_get(v___x_5344_, 0);
                    leanh::lean_inc(v_a_5345_);
                    leanh::lean_dec_ref_known(v___x_5344_, 1);
                    v___x_5346_ = (leanh::lean_unbox(v_a_5345_) as u8);
                    if v___x_5346_ == 0 {
                        v___x_5347_ =
                            l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_5338_, v___y_5231_);
                        if leanh::lean_obj_tag(v___x_5347_) == 0 {
                            v_a_5348_ = leanh::lean_ctor_get(v___x_5347_, 0);
                            leanh::lean_inc(v_a_5348_);
                            leanh::lean_dec_ref_known(v___x_5347_, 1);
                            v___x_5349_ = (leanh::lean_unbox(v_a_5348_) as u8);
                            if v___x_5349_ == 0 {
                                leanh::lean_dec(v_a_5345_);
                                leanh::lean_del_object(v___x_5342_);
                                v___x_5350_ = leanh::lean_box(0);
                                v___x_5351_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
                                leanh::lean_inc_ref_n(v_proof_5339_, 2);
                                leanh::lean_inc_ref_n(v_arg_5249_, 2);
                                leanh::lean_inc_ref_n(v_e_x27_5338_, 2);
                                leanh::lean_inc_ref_n(v_arg_5252_, 3);
                                v___x_5352_ = l_Lean_mkApp4(
                                    v___x_5351_,
                                    v_arg_5252_,
                                    v_e_x27_5338_,
                                    v_arg_5249_,
                                    v_proof_5339_,
                                );
                                v___x_5353_ = leanh::lean_unsigned_to_nat(4);
                                v___x_5354_ = l_Lean_Expr_getBoundedAppFn(v___x_5353_, v_e_5227_);
                                v___x_5355_ = leanh::lean_box((v___x_5258_) as usize);
                                v___x_5356_ =
                                    leanh::lean_box((v_contextDependent_5340_) as usize);
                                leanh::lean_inc_ref(v___x_5352_);
                                leanh::lean_inc_ref_n(v_arg_5243_, 2);
                                leanh::lean_inc_ref_n(v_arg_5246_, 2);
                                v___f_5357_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__1___boxed as *mut core::ffi::c_void, 22, 12);
                                leanh::lean_closure_set(v___f_5357_, 0, v_proof_5339_);
                                leanh::lean_closure_set(v___f_5357_, 1, v___x_5350_);
                                leanh::lean_closure_set(v___f_5357_, 2, v_arg_5252_);
                                leanh::lean_closure_set(v___f_5357_, 3, v_e_x27_5338_);
                                leanh::lean_closure_set(v___f_5357_, 4, v_arg_5246_);
                                leanh::lean_closure_set(v___f_5357_, 5, v_a_5348_);
                                leanh::lean_closure_set(v___f_5357_, 6, v_arg_5243_);
                                leanh::lean_closure_set(v___f_5357_, 7, v___x_5354_);
                                leanh::lean_closure_set(v___f_5357_, 8, v___x_5352_);
                                leanh::lean_closure_set(v___f_5357_, 9, v_e_5227_);
                                leanh::lean_closure_set(v___f_5357_, 10, v___x_5355_);
                                leanh::lean_closure_set(v___f_5357_, 11, v___x_5356_);
                                leanh::lean_inc_ref(v_arg_5255_);
                                leanh::lean_inc_ref(v___x_5256_);
                                v___x_5358_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidableCongr___boxed as *mut core::ffi::c_void, 20, 10);
                                leanh::lean_closure_set(v___x_5358_, 0, v___x_5256_);
                                leanh::lean_closure_set(v___x_5358_, 1, v_arg_5255_);
                                leanh::lean_closure_set(v___x_5358_, 2, v_arg_5252_);
                                leanh::lean_closure_set(v___x_5358_, 3, v_arg_5249_);
                                leanh::lean_closure_set(v___x_5358_, 4, v_arg_5246_);
                                leanh::lean_closure_set(v___x_5358_, 5, v_arg_5243_);
                                leanh::lean_closure_set(v___x_5358_, 6, v_e_x27_5338_);
                                leanh::lean_closure_set(v___x_5358_, 7, v_proof_5339_);
                                leanh::lean_closure_set(v___x_5358_, 8, v___x_5352_);
                                leanh::lean_closure_set(v___x_5358_, 9, v___f_5357_);
                                v___x_5359_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDIteDecidable(v___x_5256_, v_arg_5255_, v_arg_5252_, v_arg_5249_, v_arg_5246_, v_arg_5243_, v___x_5358_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_, v___y_5232_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
                                leanh::lean_dec_ref(v___x_5256_);
                                return v___x_5359_;
                            } else {
                                leanh::lean_dec(v_a_5348_);
                                leanh::lean_dec_ref(v_e_x27_5338_);
                                leanh::lean_dec_ref(v___x_5256_);
                                leanh::lean_dec_ref(v_arg_5255_);
                                leanh::lean_dec_ref(v_arg_5249_);
                                leanh::lean_dec_ref(v_arg_5246_);
                                leanh::lean_inc_ref(v_proof_5339_);
                                v___x_5360_ =
                                    l_Lean_Meta_mkOfEqFalseCore(v_arg_5252_, v_proof_5339_);
                                v___x_5361_ =
                                    l_Lean_Meta_Sym_shareCommon___redArg(v___x_5360_, v___y_5232_);
                                if leanh::lean_obj_tag(v___x_5361_) == 0 {
                                    v_a_5362_ = leanh::lean_ctor_get(v___x_5361_, 0);
                                    leanh::lean_inc(v_a_5362_);
                                    leanh::lean_dec_ref_known(v___x_5361_, 1);
                                    v___x_5363_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_5364_ = lean_mk_empty_array_with_capacity(v___x_5363_);
                                    v___x_5365_ = lean_array_push(v___x_5364_, v_a_5362_);
                                    v___x_5366_ = (leanh::lean_unbox(v_a_5345_) as u8);
                                    v___x_5367_ = (leanh::lean_unbox(v_a_5345_) as u8);
                                    v___x_5368_ = l_Lean_Expr_betaRev(
                                        v_arg_5243_,
                                        v___x_5365_,
                                        v___x_5366_,
                                        v___x_5367_,
                                    );
                                    leanh::lean_dec_ref(v___x_5365_);
                                    v___x_5369_ = l_Lean_Meta_Sym_shareCommonInc___redArg(
                                        v___x_5368_,
                                        v___y_5232_,
                                    );
                                    if leanh::lean_obj_tag(v___x_5369_) == 0 {
                                        v_a_5370_ = leanh::lean_ctor_get(v___x_5369_, 0);
                                        v_isSharedCheck_5384_ =
                                            (!leanh::lean_is_exclusive(v___x_5369_)) as u8;
                                        if v_isSharedCheck_5384_ == 0 {
                                            v___x_5372_ = v___x_5369_;
                                            v_isShared_5373_ = v_isSharedCheck_5384_;
                                            state = 15;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5370_);
                                            leanh::lean_dec(v___x_5369_);
                                            v___x_5372_ = leanh::lean_box(0);
                                            v_isShared_5373_ = v_isSharedCheck_5384_;
                                            state = 15;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_5345_);
                                        leanh::lean_del_object(v___x_5342_);
                                        leanh::lean_dec_ref(v_proof_5339_);
                                        leanh::lean_dec_ref(v_e_5227_);
                                        v_a_5385_ = leanh::lean_ctor_get(v___x_5369_, 0);
                                        v_isSharedCheck_5392_ =
                                            (!leanh::lean_is_exclusive(v___x_5369_)) as u8;
                                        if v_isSharedCheck_5392_ == 0 {
                                            v___x_5387_ = v___x_5369_;
                                            v_isShared_5388_ = v_isSharedCheck_5392_;
                                            state = 18;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5385_);
                                            leanh::lean_dec(v___x_5369_);
                                            v___x_5387_ = leanh::lean_box(0);
                                            v_isShared_5388_ = v_isSharedCheck_5392_;
                                            state = 18;
                                            continue;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_5345_);
                                    leanh::lean_del_object(v___x_5342_);
                                    leanh::lean_dec_ref(v_proof_5339_);
                                    leanh::lean_dec_ref(v_arg_5243_);
                                    leanh::lean_dec_ref(v_e_5227_);
                                    v_a_5393_ = leanh::lean_ctor_get(v___x_5361_, 0);
                                    v_isSharedCheck_5400_ =
                                        (!leanh::lean_is_exclusive(v___x_5361_)) as u8;
                                    if v_isSharedCheck_5400_ == 0 {
                                        v___x_5395_ = v___x_5361_;
                                        v_isShared_5396_ = v_isSharedCheck_5400_;
                                        state = 20;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5393_);
                                        leanh::lean_dec(v___x_5361_);
                                        v___x_5395_ = leanh::lean_box(0);
                                        v_isShared_5396_ = v_isSharedCheck_5400_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_5345_);
                            leanh::lean_del_object(v___x_5342_);
                            leanh::lean_dec_ref(v_proof_5339_);
                            leanh::lean_dec_ref(v_e_x27_5338_);
                            leanh::lean_dec_ref(v___x_5256_);
                            leanh::lean_dec_ref(v_arg_5255_);
                            leanh::lean_dec_ref(v_arg_5252_);
                            leanh::lean_dec_ref(v_arg_5249_);
                            leanh::lean_dec_ref(v_arg_5246_);
                            leanh::lean_dec_ref(v_arg_5243_);
                            leanh::lean_dec_ref(v_e_5227_);
                            v_a_5401_ = leanh::lean_ctor_get(v___x_5347_, 0);
                            v_isSharedCheck_5408_ =
                                (!leanh::lean_is_exclusive(v___x_5347_)) as u8;
                            if v_isSharedCheck_5408_ == 0 {
                                v___x_5403_ = v___x_5347_;
                                v_isShared_5404_ = v_isSharedCheck_5408_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5401_);
                                leanh::lean_dec(v___x_5347_);
                                v___x_5403_ = leanh::lean_box(0);
                                v_isShared_5404_ = v_isSharedCheck_5408_;
                                state = 22;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5345_);
                        leanh::lean_dec_ref(v_e_x27_5338_);
                        leanh::lean_dec_ref(v___x_5256_);
                        leanh::lean_dec_ref(v_arg_5255_);
                        leanh::lean_dec_ref(v_arg_5249_);
                        leanh::lean_dec_ref(v_arg_5243_);
                        leanh::lean_inc_ref(v_proof_5339_);
                        v___x_5409_ = l_Lean_Meta_mkOfEqTrueCore(v_arg_5252_, v_proof_5339_);
                        v___x_5410_ =
                            l_Lean_Meta_Sym_shareCommon___redArg(v___x_5409_, v___y_5232_);
                        if leanh::lean_obj_tag(v___x_5410_) == 0 {
                            v_a_5411_ = leanh::lean_ctor_get(v___x_5410_, 0);
                            leanh::lean_inc(v_a_5411_);
                            leanh::lean_dec_ref_known(v___x_5410_, 1);
                            v___x_5412_ = leanh::lean_unsigned_to_nat(1);
                            v___x_5413_ = lean_mk_empty_array_with_capacity(v___x_5412_);
                            v___x_5414_ = lean_array_push(v___x_5413_, v_a_5411_);
                            v___x_5415_ = l_Lean_Expr_betaRev(
                                v_arg_5246_,
                                v___x_5414_,
                                v___x_5226_,
                                v___x_5226_,
                            );
                            leanh::lean_dec_ref(v___x_5414_);
                            v___x_5416_ =
                                l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_5415_, v___y_5232_);
                            if leanh::lean_obj_tag(v___x_5416_) == 0 {
                                v_a_5417_ = leanh::lean_ctor_get(v___x_5416_, 0);
                                v_isSharedCheck_5430_ =
                                    (!leanh::lean_is_exclusive(v___x_5416_)) as u8;
                                if v_isSharedCheck_5430_ == 0 {
                                    v___x_5419_ = v___x_5416_;
                                    v_isShared_5420_ = v_isSharedCheck_5430_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5417_);
                                    leanh::lean_dec(v___x_5416_);
                                    v___x_5419_ = leanh::lean_box(0);
                                    v_isShared_5420_ = v_isSharedCheck_5430_;
                                    state = 24;
                                    continue;
                                }
                            } else {
                                leanh::lean_del_object(v___x_5342_);
                                leanh::lean_dec_ref(v_proof_5339_);
                                leanh::lean_dec_ref(v_e_5227_);
                                v_a_5431_ = leanh::lean_ctor_get(v___x_5416_, 0);
                                v_isSharedCheck_5438_ =
                                    (!leanh::lean_is_exclusive(v___x_5416_)) as u8;
                                if v_isSharedCheck_5438_ == 0 {
                                    v___x_5433_ = v___x_5416_;
                                    v_isShared_5434_ = v_isSharedCheck_5438_;
                                    state = 27;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5431_);
                                    leanh::lean_dec(v___x_5416_);
                                    v___x_5433_ = leanh::lean_box(0);
                                    v_isShared_5434_ = v_isSharedCheck_5438_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_5342_);
                            leanh::lean_dec_ref(v_proof_5339_);
                            leanh::lean_dec_ref(v_arg_5246_);
                            leanh::lean_dec_ref(v_e_5227_);
                            v_a_5439_ = leanh::lean_ctor_get(v___x_5410_, 0);
                            v_isSharedCheck_5446_ =
                                (!leanh::lean_is_exclusive(v___x_5410_)) as u8;
                            if v_isSharedCheck_5446_ == 0 {
                                v___x_5441_ = v___x_5410_;
                                v_isShared_5442_ = v_isSharedCheck_5446_;
                                state = 29;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5439_);
                                leanh::lean_dec(v___x_5410_);
                                v___x_5441_ = leanh::lean_box(0);
                                v_isShared_5442_ = v_isSharedCheck_5446_;
                                state = 29;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5342_);
                    leanh::lean_dec_ref(v_proof_5339_);
                    leanh::lean_dec_ref(v_e_x27_5338_);
                    leanh::lean_dec_ref(v___x_5256_);
                    leanh::lean_dec_ref(v_arg_5255_);
                    leanh::lean_dec_ref(v_arg_5252_);
                    leanh::lean_dec_ref(v_arg_5249_);
                    leanh::lean_dec_ref(v_arg_5246_);
                    leanh::lean_dec_ref(v_arg_5243_);
                    leanh::lean_dec_ref(v_e_5227_);
                    v_a_5447_ = leanh::lean_ctor_get(v___x_5344_, 0);
                    v_isSharedCheck_5454_ = (!leanh::lean_is_exclusive(v___x_5344_)) as u8;
                    if v_isSharedCheck_5454_ == 0 {
                        v___x_5449_ = v___x_5344_;
                        v_isShared_5450_ = v_isSharedCheck_5454_;
                        state = 31;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5447_);
                        leanh::lean_dec(v___x_5344_);
                        v___x_5449_ = leanh::lean_box(0);
                        v_isShared_5450_ = v_isSharedCheck_5454_;
                        state = 31;
                        continue;
                    }
                }
            }
            15 => {
                v___x_5374_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__14;
                v___x_5375_ = l_Lean_Expr_replaceFn(v_e_5227_, v___x_5374_);
                v___x_5376_ = l_Lean_Expr_app___override(v___x_5375_, v_proof_5339_);
                if v_isShared_5343_ == 0 {
                    leanh::lean_ctor_set(v___x_5342_, 1, v___x_5376_);
                    leanh::lean_ctor_set(v___x_5342_, 0, v_a_5370_);
                    v___x_5378_ = v___x_5342_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5370_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 1, v___x_5376_);
                    v___x_5378_ = v_reuseFailAlloc_5383_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_5379_ = (leanh::lean_unbox(v_a_5345_) as u8);
                leanh::lean_dec(v_a_5345_);
                leanh::lean_ctor_set_uint8(
                    v___x_5378_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5379_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5378_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_5340_,
                );
                if v_isShared_5373_ == 0 {
                    leanh::lean_ctor_set(v___x_5372_, 0, v___x_5378_);
                    v___x_5381_ = v___x_5372_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5382_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5378_);
                    v___x_5381_ = v_reuseFailAlloc_5382_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5381_;
            }
            18 => {
                if v_isShared_5388_ == 0 {
                    v___x_5390_ = v___x_5387_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5391_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5391_, 0, v_a_5385_);
                    v___x_5390_ = v_reuseFailAlloc_5391_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5390_;
            }
            20 => {
                if v_isShared_5396_ == 0 {
                    v___x_5398_ = v___x_5395_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5399_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
                    v___x_5398_ = v_reuseFailAlloc_5399_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_5398_;
            }
            22 => {
                if v_isShared_5404_ == 0 {
                    v___x_5406_ = v___x_5403_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5407_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
                    v___x_5406_ = v_reuseFailAlloc_5407_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5406_;
            }
            24 => {
                v___x_5421_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___closed__16;
                v___x_5422_ = l_Lean_Expr_replaceFn(v_e_5227_, v___x_5421_);
                v___x_5423_ = l_Lean_Expr_app___override(v___x_5422_, v_proof_5339_);
                if v_isShared_5343_ == 0 {
                    leanh::lean_ctor_set(v___x_5342_, 1, v___x_5423_);
                    leanh::lean_ctor_set(v___x_5342_, 0, v_a_5417_);
                    v___x_5425_ = v___x_5342_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5429_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5429_, 0, v_a_5417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5429_, 1, v___x_5423_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5429_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_5340_,
                    );
                    v___x_5425_ = v_reuseFailAlloc_5429_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                leanh::lean_ctor_set_uint8(
                    v___x_5425_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5226_,
                );
                if v_isShared_5420_ == 0 {
                    leanh::lean_ctor_set(v___x_5419_, 0, v___x_5425_);
                    v___x_5427_ = v___x_5419_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5428_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5425_);
                    v___x_5427_ = v_reuseFailAlloc_5428_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5427_;
            }
            27 => {
                if v_isShared_5434_ == 0 {
                    v___x_5436_ = v___x_5433_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5437_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5437_, 0, v_a_5431_);
                    v___x_5436_ = v_reuseFailAlloc_5437_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5436_;
            }
            29 => {
                if v_isShared_5442_ == 0 {
                    v___x_5444_ = v___x_5441_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5445_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
                    v___x_5444_ = v_reuseFailAlloc_5445_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5444_;
            }
            31 => {
                if v_isShared_5450_ == 0 {
                    v___x_5452_ = v___x_5449_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
                    v___x_5452_ = v_reuseFailAlloc_5453_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed(
    mut v___x_5456_: *mut leanh::LeanObject,
    mut v_e_5457_: *mut leanh::LeanObject,
    mut v___y_5458_: *mut leanh::LeanObject,
    mut v___y_5459_: *mut leanh::LeanObject,
    mut v___y_5460_: *mut leanh::LeanObject,
    mut v___y_5461_: *mut leanh::LeanObject,
    mut v___y_5462_: *mut leanh::LeanObject,
    mut v___y_5463_: *mut leanh::LeanObject,
    mut v___y_5464_: *mut leanh::LeanObject,
    mut v___y_5465_: *mut leanh::LeanObject,
    mut v___y_5466_: *mut leanh::LeanObject,
    mut v___y_5467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_32876__boxed_5468_: u8 = 0;
    let mut v_res_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_32876__boxed_5468_ = (leanh::lean_unbox(v___x_5456_) as u8);
    v_res_5469_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0(
            v___x_32876__boxed_5468_,
            v_e_5457_,
            v___y_5458_,
            v___y_5459_,
            v___y_5460_,
            v___y_5461_,
            v___y_5462_,
            v___y_5463_,
            v___y_5464_,
            v___y_5465_,
            v___y_5466_,
        );
    leanh::lean_dec(v___y_5466_);
    leanh::lean_dec_ref(v___y_5465_);
    leanh::lean_dec(v___y_5464_);
    leanh::lean_dec_ref(v___y_5463_);
    leanh::lean_dec(v___y_5462_);
    leanh::lean_dec_ref(v___y_5461_);
    leanh::lean_dec(v___y_5460_);
    leanh::lean_dec_ref(v___y_5459_);
    leanh::lean_dec(v___y_5458_);
    return v_res_5469_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(
    mut v_e_5470_: *mut leanh::LeanObject,
    mut v_a_5471_: *mut leanh::LeanObject,
    mut v_a_5472_: *mut leanh::LeanObject,
    mut v_a_5473_: *mut leanh::LeanObject,
    mut v_a_5474_: *mut leanh::LeanObject,
    mut v_a_5475_: *mut leanh::LeanObject,
    mut v_a_5476_: *mut leanh::LeanObject,
    mut v_a_5477_: *mut leanh::LeanObject,
    mut v_a_5478_: *mut leanh::LeanObject,
    mut v_a_5479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numArgs_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: u8 = 0;
    v_numArgs_5481_ = l_Lean_Expr_getAppNumArgs(v_e_5470_);
    v___x_5482_ = leanh::lean_unsigned_to_nat(5);
    v___x_5483_ = lean_nat_dec_lt(v_numArgs_5481_, v___x_5482_);
    if v___x_5483_ == 0 {
        let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5487_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_5484_ = leanh::lean_box((v___x_5483_) as usize);
        v___f_5485_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___lam__0___boxed as *mut core::ffi::c_void, 12, 1);
        leanh::lean_closure_set(v___f_5485_, 0, v___x_5484_);
        v___x_5486_ = lean_nat_sub(v_numArgs_5481_, v___x_5482_);
        leanh::lean_dec(v_numArgs_5481_);
        v___x_5487_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(
            v_e_5470_,
            v___x_5486_,
            v___f_5485_,
            v_a_5471_,
            v_a_5472_,
            v_a_5473_,
            v_a_5474_,
            v_a_5475_,
            v_a_5476_,
            v_a_5477_,
            v_a_5478_,
            v_a_5479_,
        );
        leanh::lean_dec(v___x_5486_);
        return v___x_5487_;
    } else {
        let mut v___x_5488_: u8 = 0;
        let mut v___x_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_numArgs_5481_);
        leanh::lean_dec_ref(v_e_5470_);
        v___x_5488_ = 0;
        v___x_5489_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
        leanh::lean_ctor_set_uint8(v___x_5489_, 0 as u32, v___x_5483_);
        leanh::lean_ctor_set_uint8(v___x_5489_, 1 as u32, v___x_5488_);
        v___x_5490_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_5490_, 0, v___x_5489_);
        return v___x_5490_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed(
    mut v_e_5491_: *mut leanh::LeanObject,
    mut v_a_5492_: *mut leanh::LeanObject,
    mut v_a_5493_: *mut leanh::LeanObject,
    mut v_a_5494_: *mut leanh::LeanObject,
    mut v_a_5495_: *mut leanh::LeanObject,
    mut v_a_5496_: *mut leanh::LeanObject,
    mut v_a_5497_: *mut leanh::LeanObject,
    mut v_a_5498_: *mut leanh::LeanObject,
    mut v_a_5499_: *mut leanh::LeanObject,
    mut v_a_5500_: *mut leanh::LeanObject,
    mut v_a_5501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5502_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv(
        v_e_5491_, v_a_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_,
        v_a_5499_, v_a_5500_,
    );
    leanh::lean_dec(v_a_5500_);
    leanh::lean_dec_ref(v_a_5499_);
    leanh::lean_dec(v_a_5498_);
    leanh::lean_dec_ref(v_a_5497_);
    leanh::lean_dec(v_a_5496_);
    leanh::lean_dec_ref(v_a_5495_);
    leanh::lean_dec(v_a_5494_);
    leanh::lean_dec_ref(v_a_5493_);
    leanh::lean_dec(v_a_5492_);
    return v_res_5502_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_()
-> *mut leanh::LeanObject {
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5521_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_;
    v___x_5522_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_;
    v___x_5523_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed
            as *mut core::ffi::c_void,
        11,
        0,
    );
    v___x_5524_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_5521_, v___x_5522_, v___x_5523_);
    return v___x_5524_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16____boxed(
    mut v_a_5525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5526_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_();
    return v_res_5526_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_()
-> *mut leanh::LeanObject {
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: u8 = 0;
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5528_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_;
    v___x_5529_ = 0;
    v___x_5530_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___boxed
            as *mut core::ffi::c_void,
        11,
        0,
    );
    v___x_5531_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_5528_, v___x_5529_, v___x_5530_);
    return v___x_5531_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18____boxed(
    mut v_a_5532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5533_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_();
    return v_res_5533_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5539_ = leanh::lean_box(0);
    v___x_5540_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__1;
    v___x_5541_ = l_Lean_mkConst(v___x_5540_, v___x_5539_);
    return v___x_5541_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5547_ = leanh::lean_box(0);
    v___x_5548_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__4;
    v___x_5549_ = l_Lean_mkConst(v___x_5548_, v___x_5547_);
    return v___x_5549_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(
    mut v_p_5550_: *mut leanh::LeanObject,
    mut v_inst_5551_: *mut leanh::LeanObject,
    mut v_instToMatch_5552_: *mut leanh::LeanObject,
    mut v_fallback_5553_: *mut leanh::LeanObject,
    mut v_a_5554_: *mut leanh::LeanObject,
    mut v_a_5555_: *mut leanh::LeanObject,
    mut v_a_5556_: *mut leanh::LeanObject,
    mut v_a_5557_: *mut leanh::LeanObject,
    mut v_a_5558_: *mut leanh::LeanObject,
    mut v_a_5559_: *mut leanh::LeanObject,
    mut v_a_5560_: *mut leanh::LeanObject,
    mut v_a_5561_: *mut leanh::LeanObject,
    mut v_a_5562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: u8 = 0;
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: u8 = 0;
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: u8 = 0;
    let mut v___x_5578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5583_: u8 = 0;
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5590_: u8 = 0;
    let mut v_a_5591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5598_: u8 = 0;
    let mut v___x_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5603_: u8 = 0;
    let mut v___x_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: u8 = 0;
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5611_: u8 = 0;
    let mut v_a_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5615_: u8 = 0;
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5619_: u8 = 0;
    let mut v_a_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5623_: u8 = 0;
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5564_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_instToMatch_5552_, v_a_5560_);
                if leanh::lean_obj_tag(v___x_5564_) == 0 {
                    v_a_5565_ = leanh::lean_ctor_get(v___x_5564_, 0);
                    leanh::lean_inc(v_a_5565_);
                    leanh::lean_dec_ref_known(v___x_5564_, 1);
                    v___x_5566_ = l_Lean_Expr_cleanupAnnotations(v_a_5565_);
                    v___x_5567_ = l_Lean_Expr_isApp(v___x_5566_);
                    if v___x_5567_ == 0 {
                        leanh::lean_dec_ref(v___x_5566_);
                        leanh::lean_dec_ref(v_inst_5551_);
                        leanh::lean_dec_ref(v_p_5550_);
                        leanh::lean_inc(v_a_5562_);
                        leanh::lean_inc_ref(v_a_5561_);
                        leanh::lean_inc(v_a_5560_);
                        leanh::lean_inc_ref(v_a_5559_);
                        leanh::lean_inc(v_a_5558_);
                        leanh::lean_inc_ref(v_a_5557_);
                        leanh::lean_inc(v_a_5556_);
                        leanh::lean_inc_ref(v_a_5555_);
                        leanh::lean_inc(v_a_5554_);
                        v___x_5568_ = leanh::lean_apply_10(
                            v_fallback_5553_,
                            v_a_5554_,
                            v_a_5555_,
                            v_a_5556_,
                            v_a_5557_,
                            v_a_5558_,
                            v_a_5559_,
                            v_a_5560_,
                            v_a_5561_,
                            v_a_5562_,
                            leanh::lean_box(0),
                        );
                        return v___x_5568_;
                    } else {
                        v_arg_5569_ = leanh::lean_ctor_get(v___x_5566_, 1);
                        leanh::lean_inc_ref(v_arg_5569_);
                        v___x_5570_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5566_);
                        v___x_5571_ = l_Lean_Expr_isApp(v___x_5570_);
                        if v___x_5571_ == 0 {
                            leanh::lean_dec_ref(v___x_5570_);
                            leanh::lean_dec_ref(v_arg_5569_);
                            leanh::lean_dec_ref(v_inst_5551_);
                            leanh::lean_dec_ref(v_p_5550_);
                            leanh::lean_inc(v_a_5562_);
                            leanh::lean_inc_ref(v_a_5561_);
                            leanh::lean_inc(v_a_5560_);
                            leanh::lean_inc_ref(v_a_5559_);
                            leanh::lean_inc(v_a_5558_);
                            leanh::lean_inc_ref(v_a_5557_);
                            leanh::lean_inc(v_a_5556_);
                            leanh::lean_inc_ref(v_a_5555_);
                            leanh::lean_inc(v_a_5554_);
                            v___x_5572_ = leanh::lean_apply_10(
                                v_fallback_5553_,
                                v_a_5554_,
                                v_a_5555_,
                                v_a_5556_,
                                v_a_5557_,
                                v_a_5558_,
                                v_a_5559_,
                                v_a_5560_,
                                v_a_5561_,
                                v_a_5562_,
                                leanh::lean_box(0),
                            );
                            return v___x_5572_;
                        } else {
                            v___x_5573_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5570_);
                            v___x_5574_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1;
                            v___x_5575_ = l_Lean_Expr_isConstOf(v___x_5573_, v___x_5574_);
                            if v___x_5575_ == 0 {
                                v___x_5576_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3;
                                v___x_5577_ = l_Lean_Expr_isConstOf(v___x_5573_, v___x_5576_);
                                leanh::lean_dec_ref(v___x_5573_);
                                if v___x_5577_ == 0 {
                                    leanh::lean_dec_ref(v_arg_5569_);
                                    leanh::lean_dec_ref(v_inst_5551_);
                                    leanh::lean_dec_ref(v_p_5550_);
                                    leanh::lean_inc(v_a_5562_);
                                    leanh::lean_inc_ref(v_a_5561_);
                                    leanh::lean_inc(v_a_5560_);
                                    leanh::lean_inc_ref(v_a_5559_);
                                    leanh::lean_inc(v_a_5558_);
                                    leanh::lean_inc_ref(v_a_5557_);
                                    leanh::lean_inc(v_a_5556_);
                                    leanh::lean_inc_ref(v_a_5555_);
                                    leanh::lean_inc(v_a_5554_);
                                    v___x_5578_ = leanh::lean_apply_10(
                                        v_fallback_5553_,
                                        v_a_5554_,
                                        v_a_5555_,
                                        v_a_5556_,
                                        v_a_5557_,
                                        v_a_5558_,
                                        v_a_5559_,
                                        v_a_5560_,
                                        v_a_5561_,
                                        v_a_5562_,
                                        leanh::lean_box(0),
                                    );
                                    return v___x_5578_;
                                } else {
                                    leanh::lean_dec_ref(v_fallback_5553_);
                                    v___x_5579_ =
                                        l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_5557_);
                                    if leanh::lean_obj_tag(v___x_5579_) == 0 {
                                        v_a_5580_ = leanh::lean_ctor_get(v___x_5579_, 0);
                                        v_isSharedCheck_5590_ =
                                            (!leanh::lean_is_exclusive(v___x_5579_)) as u8;
                                        if v_isSharedCheck_5590_ == 0 {
                                            v___x_5582_ = v___x_5579_;
                                            v_isShared_5583_ = v_isSharedCheck_5590_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5580_);
                                            leanh::lean_dec(v___x_5579_);
                                            v___x_5582_ = leanh::lean_box(0);
                                            v_isShared_5583_ = v_isSharedCheck_5590_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_arg_5569_);
                                        leanh::lean_dec_ref(v_inst_5551_);
                                        leanh::lean_dec_ref(v_p_5550_);
                                        v_a_5591_ = leanh::lean_ctor_get(v___x_5579_, 0);
                                        v_isSharedCheck_5598_ =
                                            (!leanh::lean_is_exclusive(v___x_5579_)) as u8;
                                        if v_isSharedCheck_5598_ == 0 {
                                            v___x_5593_ = v___x_5579_;
                                            v_isShared_5594_ = v_isSharedCheck_5598_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5591_);
                                            leanh::lean_dec(v___x_5579_);
                                            v___x_5593_ = leanh::lean_box(0);
                                            v_isShared_5594_ = v_isSharedCheck_5598_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_5573_);
                                leanh::lean_dec_ref(v_fallback_5553_);
                                v___x_5599_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_5557_);
                                if leanh::lean_obj_tag(v___x_5599_) == 0 {
                                    v_a_5600_ = leanh::lean_ctor_get(v___x_5599_, 0);
                                    v_isSharedCheck_5611_ =
                                        (!leanh::lean_is_exclusive(v___x_5599_)) as u8;
                                    if v_isSharedCheck_5611_ == 0 {
                                        v___x_5602_ = v___x_5599_;
                                        v_isShared_5603_ = v_isSharedCheck_5611_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5600_);
                                        leanh::lean_dec(v___x_5599_);
                                        v___x_5602_ = leanh::lean_box(0);
                                        v_isShared_5603_ = v_isSharedCheck_5611_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_5569_);
                                    leanh::lean_dec_ref(v_inst_5551_);
                                    leanh::lean_dec_ref(v_p_5550_);
                                    v_a_5612_ = leanh::lean_ctor_get(v___x_5599_, 0);
                                    v_isSharedCheck_5619_ =
                                        (!leanh::lean_is_exclusive(v___x_5599_)) as u8;
                                    if v_isSharedCheck_5619_ == 0 {
                                        v___x_5614_ = v___x_5599_;
                                        v_isShared_5615_ = v_isSharedCheck_5619_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5612_);
                                        leanh::lean_dec(v___x_5599_);
                                        v___x_5614_ = leanh::lean_box(0);
                                        v_isShared_5615_ = v_isSharedCheck_5619_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_5553_);
                    leanh::lean_dec_ref(v_inst_5551_);
                    leanh::lean_dec_ref(v_p_5550_);
                    v_a_5620_ = leanh::lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5627_ = (!leanh::lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5627_ == 0 {
                        v___x_5622_ = v___x_5564_;
                        v_isShared_5623_ = v_isSharedCheck_5627_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5620_);
                        leanh::lean_dec(v___x_5564_);
                        v___x_5622_ = leanh::lean_box(0);
                        v_isShared_5623_ = v_isSharedCheck_5627_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5584_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__2);
                v___x_5585_ = l_Lean_mkApp3(v___x_5584_, v_p_5550_, v_inst_5551_, v_arg_5569_);
                v___x_5586_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5586_, 0, v_a_5580_);
                leanh::lean_ctor_set(v___x_5586_, 1, v___x_5585_);
                leanh::lean_ctor_set_uint8(
                    v___x_5586_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5575_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5586_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_5575_,
                );
                if v_isShared_5583_ == 0 {
                    leanh::lean_ctor_set(v___x_5582_, 0, v___x_5586_);
                    v___x_5588_ = v___x_5582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5586_);
                    v___x_5588_ = v_reuseFailAlloc_5589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5588_;
            }
            3 => {
                if v_isShared_5594_ == 0 {
                    v___x_5596_ = v___x_5593_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
                    v___x_5596_ = v_reuseFailAlloc_5597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5596_;
            }
            5 => {
                v___x_5604_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___closed__5);
                v___x_5605_ = l_Lean_mkApp3(v___x_5604_, v_p_5550_, v_inst_5551_, v_arg_5569_);
                v___x_5606_ = 0;
                v___x_5607_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5607_, 0, v_a_5600_);
                leanh::lean_ctor_set(v___x_5607_, 1, v___x_5605_);
                leanh::lean_ctor_set_uint8(
                    v___x_5607_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5606_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5607_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_5606_,
                );
                if v_isShared_5603_ == 0 {
                    leanh::lean_ctor_set(v___x_5602_, 0, v___x_5607_);
                    v___x_5609_ = v___x_5602_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5610_, 0, v___x_5607_);
                    v___x_5609_ = v_reuseFailAlloc_5610_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5609_;
            }
            7 => {
                if v_isShared_5615_ == 0 {
                    v___x_5617_ = v___x_5614_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5618_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5618_, 0, v_a_5612_);
                    v___x_5617_ = v_reuseFailAlloc_5618_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5617_;
            }
            9 => {
                if v_isShared_5623_ == 0 {
                    v___x_5625_ = v___x_5622_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5626_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_a_5620_);
                    v___x_5625_ = v_reuseFailAlloc_5626_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable___boxed(
    mut v_p_5628_: *mut leanh::LeanObject,
    mut v_inst_5629_: *mut leanh::LeanObject,
    mut v_instToMatch_5630_: *mut leanh::LeanObject,
    mut v_fallback_5631_: *mut leanh::LeanObject,
    mut v_a_5632_: *mut leanh::LeanObject,
    mut v_a_5633_: *mut leanh::LeanObject,
    mut v_a_5634_: *mut leanh::LeanObject,
    mut v_a_5635_: *mut leanh::LeanObject,
    mut v_a_5636_: *mut leanh::LeanObject,
    mut v_a_5637_: *mut leanh::LeanObject,
    mut v_a_5638_: *mut leanh::LeanObject,
    mut v_a_5639_: *mut leanh::LeanObject,
    mut v_a_5640_: *mut leanh::LeanObject,
    mut v_a_5641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5642_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(
            v_p_5628_,
            v_inst_5629_,
            v_instToMatch_5630_,
            v_fallback_5631_,
            v_a_5632_,
            v_a_5633_,
            v_a_5634_,
            v_a_5635_,
            v_a_5636_,
            v_a_5637_,
            v_a_5638_,
            v_a_5639_,
            v_a_5640_,
        );
    leanh::lean_dec(v_a_5640_);
    leanh::lean_dec_ref(v_a_5639_);
    leanh::lean_dec(v_a_5638_);
    leanh::lean_dec_ref(v_a_5637_);
    leanh::lean_dec(v_a_5636_);
    leanh::lean_dec_ref(v_a_5635_);
    leanh::lean_dec(v_a_5634_);
    leanh::lean_dec_ref(v_a_5633_);
    leanh::lean_dec(v_a_5632_);
    return v_res_5642_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5648_ = leanh::lean_box(0);
    v___x_5649_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__1;
    v___x_5650_ = l_Lean_mkConst(v___x_5649_, v___x_5648_);
    return v___x_5650_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5656_ = leanh::lean_box(0);
    v___x_5657_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__4;
    v___x_5658_ = l_Lean_mkConst(v___x_5657_, v___x_5656_);
    return v___x_5658_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(
    mut v_p_5659_: *mut leanh::LeanObject,
    mut v_p_x27_5660_: *mut leanh::LeanObject,
    mut v_h_5661_: *mut leanh::LeanObject,
    mut v_inst_5662_: *mut leanh::LeanObject,
    mut v_inst_x27_5663_: *mut leanh::LeanObject,
    mut v_fallback_5664_: *mut leanh::LeanObject,
    mut v_a_5665_: *mut leanh::LeanObject,
    mut v_a_5666_: *mut leanh::LeanObject,
    mut v_a_5667_: *mut leanh::LeanObject,
    mut v_a_5668_: *mut leanh::LeanObject,
    mut v_a_5669_: *mut leanh::LeanObject,
    mut v_a_5670_: *mut leanh::LeanObject,
    mut v_a_5671_: *mut leanh::LeanObject,
    mut v_a_5672_: *mut leanh::LeanObject,
    mut v_a_5673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: u8 = 0;
    let mut v___x_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: u8 = 0;
    let mut v___x_5683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: u8 = 0;
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: u8 = 0;
    let mut v___x_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5694_: u8 = 0;
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5701_: u8 = 0;
    let mut v_a_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5705_: u8 = 0;
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5709_: u8 = 0;
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: u8 = 0;
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5722_: u8 = 0;
    let mut v_a_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5730_: u8 = 0;
    let mut v_a_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5734_: u8 = 0;
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5675_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_inst_x27_5663_, v_a_5671_);
                if leanh::lean_obj_tag(v___x_5675_) == 0 {
                    v_a_5676_ = leanh::lean_ctor_get(v___x_5675_, 0);
                    leanh::lean_inc(v_a_5676_);
                    leanh::lean_dec_ref_known(v___x_5675_, 1);
                    v___x_5677_ = l_Lean_Expr_cleanupAnnotations(v_a_5676_);
                    v___x_5678_ = l_Lean_Expr_isApp(v___x_5677_);
                    if v___x_5678_ == 0 {
                        leanh::lean_dec_ref(v___x_5677_);
                        leanh::lean_dec_ref(v_inst_5662_);
                        leanh::lean_dec_ref(v_h_5661_);
                        leanh::lean_dec_ref(v_p_x27_5660_);
                        leanh::lean_dec_ref(v_p_5659_);
                        leanh::lean_inc(v_a_5673_);
                        leanh::lean_inc_ref(v_a_5672_);
                        leanh::lean_inc(v_a_5671_);
                        leanh::lean_inc_ref(v_a_5670_);
                        leanh::lean_inc(v_a_5669_);
                        leanh::lean_inc_ref(v_a_5668_);
                        leanh::lean_inc(v_a_5667_);
                        leanh::lean_inc_ref(v_a_5666_);
                        leanh::lean_inc(v_a_5665_);
                        v___x_5679_ = leanh::lean_apply_10(
                            v_fallback_5664_,
                            v_a_5665_,
                            v_a_5666_,
                            v_a_5667_,
                            v_a_5668_,
                            v_a_5669_,
                            v_a_5670_,
                            v_a_5671_,
                            v_a_5672_,
                            v_a_5673_,
                            leanh::lean_box(0),
                        );
                        return v___x_5679_;
                    } else {
                        v_arg_5680_ = leanh::lean_ctor_get(v___x_5677_, 1);
                        leanh::lean_inc_ref(v_arg_5680_);
                        v___x_5681_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5677_);
                        v___x_5682_ = l_Lean_Expr_isApp(v___x_5681_);
                        if v___x_5682_ == 0 {
                            leanh::lean_dec_ref(v___x_5681_);
                            leanh::lean_dec_ref(v_arg_5680_);
                            leanh::lean_dec_ref(v_inst_5662_);
                            leanh::lean_dec_ref(v_h_5661_);
                            leanh::lean_dec_ref(v_p_x27_5660_);
                            leanh::lean_dec_ref(v_p_5659_);
                            leanh::lean_inc(v_a_5673_);
                            leanh::lean_inc_ref(v_a_5672_);
                            leanh::lean_inc(v_a_5671_);
                            leanh::lean_inc_ref(v_a_5670_);
                            leanh::lean_inc(v_a_5669_);
                            leanh::lean_inc_ref(v_a_5668_);
                            leanh::lean_inc(v_a_5667_);
                            leanh::lean_inc_ref(v_a_5666_);
                            leanh::lean_inc(v_a_5665_);
                            v___x_5683_ = leanh::lean_apply_10(
                                v_fallback_5664_,
                                v_a_5665_,
                                v_a_5666_,
                                v_a_5667_,
                                v_a_5668_,
                                v_a_5669_,
                                v_a_5670_,
                                v_a_5671_,
                                v_a_5672_,
                                v_a_5673_,
                                leanh::lean_box(0),
                            );
                            return v___x_5683_;
                        } else {
                            v___x_5684_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5681_);
                            v___x_5685_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__1;
                            v___x_5686_ = l_Lean_Expr_isConstOf(v___x_5684_, v___x_5685_);
                            if v___x_5686_ == 0 {
                                v___x_5687_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchIteDecidable___closed__3;
                                v___x_5688_ = l_Lean_Expr_isConstOf(v___x_5684_, v___x_5687_);
                                leanh::lean_dec_ref(v___x_5684_);
                                if v___x_5688_ == 0 {
                                    leanh::lean_dec_ref(v_arg_5680_);
                                    leanh::lean_dec_ref(v_inst_5662_);
                                    leanh::lean_dec_ref(v_h_5661_);
                                    leanh::lean_dec_ref(v_p_x27_5660_);
                                    leanh::lean_dec_ref(v_p_5659_);
                                    leanh::lean_inc(v_a_5673_);
                                    leanh::lean_inc_ref(v_a_5672_);
                                    leanh::lean_inc(v_a_5671_);
                                    leanh::lean_inc_ref(v_a_5670_);
                                    leanh::lean_inc(v_a_5669_);
                                    leanh::lean_inc_ref(v_a_5668_);
                                    leanh::lean_inc(v_a_5667_);
                                    leanh::lean_inc_ref(v_a_5666_);
                                    leanh::lean_inc(v_a_5665_);
                                    v___x_5689_ = leanh::lean_apply_10(
                                        v_fallback_5664_,
                                        v_a_5665_,
                                        v_a_5666_,
                                        v_a_5667_,
                                        v_a_5668_,
                                        v_a_5669_,
                                        v_a_5670_,
                                        v_a_5671_,
                                        v_a_5672_,
                                        v_a_5673_,
                                        leanh::lean_box(0),
                                    );
                                    return v___x_5689_;
                                } else {
                                    leanh::lean_dec_ref(v_fallback_5664_);
                                    v___x_5690_ =
                                        l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v_a_5668_);
                                    if leanh::lean_obj_tag(v___x_5690_) == 0 {
                                        v_a_5691_ = leanh::lean_ctor_get(v___x_5690_, 0);
                                        v_isSharedCheck_5701_ =
                                            (!leanh::lean_is_exclusive(v___x_5690_)) as u8;
                                        if v_isSharedCheck_5701_ == 0 {
                                            v___x_5693_ = v___x_5690_;
                                            v_isShared_5694_ = v_isSharedCheck_5701_;
                                            state = 1;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5691_);
                                            leanh::lean_dec(v___x_5690_);
                                            v___x_5693_ = leanh::lean_box(0);
                                            v_isShared_5694_ = v_isSharedCheck_5701_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_arg_5680_);
                                        leanh::lean_dec_ref(v_inst_5662_);
                                        leanh::lean_dec_ref(v_h_5661_);
                                        leanh::lean_dec_ref(v_p_x27_5660_);
                                        leanh::lean_dec_ref(v_p_5659_);
                                        v_a_5702_ = leanh::lean_ctor_get(v___x_5690_, 0);
                                        v_isSharedCheck_5709_ =
                                            (!leanh::lean_is_exclusive(v___x_5690_)) as u8;
                                        if v_isSharedCheck_5709_ == 0 {
                                            v___x_5704_ = v___x_5690_;
                                            v_isShared_5705_ = v_isSharedCheck_5709_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_5702_);
                                            leanh::lean_dec(v___x_5690_);
                                            v___x_5704_ = leanh::lean_box(0);
                                            v_isShared_5705_ = v_isSharedCheck_5709_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_5684_);
                                leanh::lean_dec_ref(v_fallback_5664_);
                                v___x_5710_ = l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v_a_5668_);
                                if leanh::lean_obj_tag(v___x_5710_) == 0 {
                                    v_a_5711_ = leanh::lean_ctor_get(v___x_5710_, 0);
                                    v_isSharedCheck_5722_ =
                                        (!leanh::lean_is_exclusive(v___x_5710_)) as u8;
                                    if v_isSharedCheck_5722_ == 0 {
                                        v___x_5713_ = v___x_5710_;
                                        v_isShared_5714_ = v_isSharedCheck_5722_;
                                        state = 5;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5711_);
                                        leanh::lean_dec(v___x_5710_);
                                        v___x_5713_ = leanh::lean_box(0);
                                        v_isShared_5714_ = v_isSharedCheck_5722_;
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_5680_);
                                    leanh::lean_dec_ref(v_inst_5662_);
                                    leanh::lean_dec_ref(v_h_5661_);
                                    leanh::lean_dec_ref(v_p_x27_5660_);
                                    leanh::lean_dec_ref(v_p_5659_);
                                    v_a_5723_ = leanh::lean_ctor_get(v___x_5710_, 0);
                                    v_isSharedCheck_5730_ =
                                        (!leanh::lean_is_exclusive(v___x_5710_)) as u8;
                                    if v_isSharedCheck_5730_ == 0 {
                                        v___x_5725_ = v___x_5710_;
                                        v_isShared_5726_ = v_isSharedCheck_5730_;
                                        state = 7;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_5723_);
                                        leanh::lean_dec(v___x_5710_);
                                        v___x_5725_ = leanh::lean_box(0);
                                        v_isShared_5726_ = v_isSharedCheck_5730_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_5664_);
                    leanh::lean_dec_ref(v_inst_5662_);
                    leanh::lean_dec_ref(v_h_5661_);
                    leanh::lean_dec_ref(v_p_x27_5660_);
                    leanh::lean_dec_ref(v_p_5659_);
                    v_a_5731_ = leanh::lean_ctor_get(v___x_5675_, 0);
                    v_isSharedCheck_5738_ = (!leanh::lean_is_exclusive(v___x_5675_)) as u8;
                    if v_isSharedCheck_5738_ == 0 {
                        v___x_5733_ = v___x_5675_;
                        v_isShared_5734_ = v_isSharedCheck_5738_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5731_);
                        leanh::lean_dec(v___x_5675_);
                        v___x_5733_ = leanh::lean_box(0);
                        v_isShared_5734_ = v_isSharedCheck_5738_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5695_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__2);
                v___x_5696_ = l_Lean_mkApp5(
                    v___x_5695_,
                    v_p_5659_,
                    v_p_x27_5660_,
                    v_h_5661_,
                    v_inst_5662_,
                    v_arg_5680_,
                );
                v___x_5697_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5697_, 0, v_a_5691_);
                leanh::lean_ctor_set(v___x_5697_, 1, v___x_5696_);
                leanh::lean_ctor_set_uint8(
                    v___x_5697_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5686_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5697_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_5686_,
                );
                if v_isShared_5694_ == 0 {
                    leanh::lean_ctor_set(v___x_5693_, 0, v___x_5697_);
                    v___x_5699_ = v___x_5693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5697_);
                    v___x_5699_ = v_reuseFailAlloc_5700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5699_;
            }
            3 => {
                if v_isShared_5705_ == 0 {
                    v___x_5707_ = v___x_5704_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5708_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5708_, 0, v_a_5702_);
                    v___x_5707_ = v_reuseFailAlloc_5708_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5707_;
            }
            5 => {
                v___x_5715_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___closed__5);
                v___x_5716_ = l_Lean_mkApp5(
                    v___x_5715_,
                    v_p_5659_,
                    v_p_x27_5660_,
                    v_h_5661_,
                    v_inst_5662_,
                    v_arg_5680_,
                );
                v___x_5717_ = 0;
                v___x_5718_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5718_, 0, v_a_5711_);
                leanh::lean_ctor_set(v___x_5718_, 1, v___x_5716_);
                leanh::lean_ctor_set_uint8(
                    v___x_5718_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5717_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5718_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_5717_,
                );
                if v_isShared_5714_ == 0 {
                    leanh::lean_ctor_set(v___x_5713_, 0, v___x_5718_);
                    v___x_5720_ = v___x_5713_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5721_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5721_, 0, v___x_5718_);
                    v___x_5720_ = v_reuseFailAlloc_5721_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5720_;
            }
            7 => {
                if v_isShared_5726_ == 0 {
                    v___x_5728_ = v___x_5725_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5729_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5729_, 0, v_a_5723_);
                    v___x_5728_ = v_reuseFailAlloc_5729_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5728_;
            }
            9 => {
                if v_isShared_5734_ == 0 {
                    v___x_5736_ = v___x_5733_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5737_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5737_, 0, v_a_5731_);
                    v___x_5736_ = v_reuseFailAlloc_5737_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr___boxed(
    mut v_p_5739_: *mut leanh::LeanObject,
    mut v_p_x27_5740_: *mut leanh::LeanObject,
    mut v_h_5741_: *mut leanh::LeanObject,
    mut v_inst_5742_: *mut leanh::LeanObject,
    mut v_inst_x27_5743_: *mut leanh::LeanObject,
    mut v_fallback_5744_: *mut leanh::LeanObject,
    mut v_a_5745_: *mut leanh::LeanObject,
    mut v_a_5746_: *mut leanh::LeanObject,
    mut v_a_5747_: *mut leanh::LeanObject,
    mut v_a_5748_: *mut leanh::LeanObject,
    mut v_a_5749_: *mut leanh::LeanObject,
    mut v_a_5750_: *mut leanh::LeanObject,
    mut v_a_5751_: *mut leanh::LeanObject,
    mut v_a_5752_: *mut leanh::LeanObject,
    mut v_a_5753_: *mut leanh::LeanObject,
    mut v_a_5754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5755_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_5739_, v_p_x27_5740_, v_h_5741_, v_inst_5742_, v_inst_x27_5743_, v_fallback_5744_, v_a_5745_, v_a_5746_, v_a_5747_, v_a_5748_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_, v_a_5753_);
    leanh::lean_dec(v_a_5753_);
    leanh::lean_dec_ref(v_a_5752_);
    leanh::lean_dec(v_a_5751_);
    leanh::lean_dec_ref(v_a_5750_);
    leanh::lean_dec(v_a_5749_);
    leanh::lean_dec_ref(v_a_5748_);
    leanh::lean_dec(v_a_5747_);
    leanh::lean_dec_ref(v_a_5746_);
    leanh::lean_dec(v_a_5745_);
    return v_res_5755_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(
    mut v_p_5756_: *mut leanh::LeanObject,
    mut v_inst_5757_: *mut leanh::LeanObject,
    mut v_fallback_5758_: *mut leanh::LeanObject,
    mut v_a_5759_: *mut leanh::LeanObject,
    mut v_a_5760_: *mut leanh::LeanObject,
    mut v_a_5761_: *mut leanh::LeanObject,
    mut v_a_5762_: *mut leanh::LeanObject,
    mut v_a_5763_: *mut leanh::LeanObject,
    mut v_a_5764_: *mut leanh::LeanObject,
    mut v_a_5765_: *mut leanh::LeanObject,
    mut v_a_5766_: *mut leanh::LeanObject,
    mut v_a_5767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5771_: u8 = 0;
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5775_: u8 = 0;
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5778_: u8 = 0;
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5783_: u8 = 0;
    let mut v_unused_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5785_: u8 = 0;
    let mut v_contextDependent_5786_: u8 = 0;
    let mut v_e_x27_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5788_: u8 = 0;
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5792_: u8 = 0;
    let mut v___x_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5800_: u8 = 0;
    let mut v_unused_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5802_: u8 = 0;
    let mut v_contextDependent_5803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_5767_);
                leanh::lean_inc_ref(v_a_5766_);
                leanh::lean_inc(v_a_5765_);
                leanh::lean_inc_ref(v_a_5764_);
                leanh::lean_inc(v_a_5763_);
                leanh::lean_inc_ref(v_a_5762_);
                leanh::lean_inc(v_a_5761_);
                leanh::lean_inc_ref(v_a_5760_);
                leanh::lean_inc(v_a_5759_);
                leanh::lean_inc_ref(v_inst_5757_);
                v___x_5769_ = lean_sym_simp(
                    v_inst_5757_,
                    v_a_5759_,
                    v_a_5760_,
                    v_a_5761_,
                    v_a_5762_,
                    v_a_5763_,
                    v_a_5764_,
                    v_a_5765_,
                    v_a_5766_,
                    v_a_5767_,
                );
                if leanh::lean_obj_tag(v___x_5769_) == 0 {
                    v_a_5770_ = leanh::lean_ctor_get(v___x_5769_, 0);
                    leanh::lean_inc(v_a_5770_);
                    leanh::lean_dec_ref_known(v___x_5769_, 1);
                    if leanh::lean_obj_tag(v_a_5770_) == 0 {
                        v_contextDependent_5771_ =
                            leanh::lean_ctor_get_uint8(v_a_5770_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_5770_, 0);
                        leanh::lean_inc_ref(v_inst_5757_);
                        v___x_5772_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_5756_, v_inst_5757_, v_inst_5757_, v_fallback_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_);
                        if leanh::lean_obj_tag(v___x_5772_) == 0 {
                            v_a_5773_ = leanh::lean_ctor_get(v___x_5772_, 0);
                            leanh::lean_inc(v_a_5773_);
                            if v_contextDependent_5771_ == 0 {
                                leanh::lean_dec(v_a_5773_);
                                return v___x_5772_;
                            } else {
                                if leanh::lean_obj_tag(v_a_5773_) == 0 {
                                    v_contextDependent_5785_ =
                                        leanh::lean_ctor_get_uint8(v_a_5773_, 1 as u32);
                                    v___y_5775_ = v_contextDependent_5785_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_contextDependent_5786_ = leanh::lean_ctor_get_uint8(
                                        v_a_5773_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_5775_ = v_contextDependent_5786_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_5772_;
                        }
                    } else {
                        v_e_x27_5787_ = leanh::lean_ctor_get(v_a_5770_, 0);
                        leanh::lean_inc_ref(v_e_x27_5787_);
                        v_contextDependent_5788_ = leanh::lean_ctor_get_uint8(
                            v_a_5770_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        leanh::lean_dec_ref_known(v_a_5770_, 2);
                        v___x_5789_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidable(v_p_5756_, v_inst_5757_, v_e_x27_5787_, v_fallback_5758_, v_a_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_, v_a_5764_, v_a_5765_, v_a_5766_, v_a_5767_);
                        if leanh::lean_obj_tag(v___x_5789_) == 0 {
                            v_a_5790_ = leanh::lean_ctor_get(v___x_5789_, 0);
                            leanh::lean_inc(v_a_5790_);
                            if v_contextDependent_5788_ == 0 {
                                leanh::lean_dec(v_a_5790_);
                                return v___x_5789_;
                            } else {
                                if leanh::lean_obj_tag(v_a_5790_) == 0 {
                                    v_contextDependent_5802_ =
                                        leanh::lean_ctor_get_uint8(v_a_5790_, 1 as u32);
                                    v___y_5792_ = v_contextDependent_5802_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_contextDependent_5803_ = leanh::lean_ctor_get_uint8(
                                        v_a_5790_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_5792_ = v_contextDependent_5803_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_5789_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_5758_);
                    leanh::lean_dec_ref(v_inst_5757_);
                    leanh::lean_dec_ref(v_p_5756_);
                    return v___x_5769_;
                }
            }
            1 => {
                if v___y_5775_ == 0 {
                    v_isSharedCheck_5783_ = (!leanh::lean_is_exclusive(v___x_5772_)) as u8;
                    if v_isSharedCheck_5783_ == 0 {
                        v_unused_5784_ = leanh::lean_ctor_get(v___x_5772_, 0);
                        leanh::lean_dec(v_unused_5784_);
                        v___x_5777_ = v___x_5772_;
                        v_isShared_5778_ = v_isSharedCheck_5783_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5772_);
                        v___x_5777_ = leanh::lean_box(0);
                        v_isShared_5778_ = v_isSharedCheck_5783_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5773_);
                    return v___x_5772_;
                }
            }
            2 => {
                v___x_5779_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_5773_);
                if v_isShared_5778_ == 0 {
                    leanh::lean_ctor_set(v___x_5777_, 0, v___x_5779_);
                    v___x_5781_ = v___x_5777_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5782_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5782_, 0, v___x_5779_);
                    v___x_5781_ = v_reuseFailAlloc_5782_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5781_;
            }
            4 => {
                if v___y_5792_ == 0 {
                    v_isSharedCheck_5800_ = (!leanh::lean_is_exclusive(v___x_5789_)) as u8;
                    if v_isSharedCheck_5800_ == 0 {
                        v_unused_5801_ = leanh::lean_ctor_get(v___x_5789_, 0);
                        leanh::lean_dec(v_unused_5801_);
                        v___x_5794_ = v___x_5789_;
                        v_isShared_5795_ = v_isSharedCheck_5800_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5789_);
                        v___x_5794_ = leanh::lean_box(0);
                        v_isShared_5795_ = v_isSharedCheck_5800_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5790_);
                    return v___x_5789_;
                }
            }
            5 => {
                v___x_5796_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_5790_);
                if v_isShared_5795_ == 0 {
                    leanh::lean_ctor_set(v___x_5794_, 0, v___x_5796_);
                    v___x_5798_ = v___x_5794_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5799_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5796_);
                    v___x_5798_ = v_reuseFailAlloc_5799_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5798_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable___boxed(
    mut v_p_5804_: *mut leanh::LeanObject,
    mut v_inst_5805_: *mut leanh::LeanObject,
    mut v_fallback_5806_: *mut leanh::LeanObject,
    mut v_a_5807_: *mut leanh::LeanObject,
    mut v_a_5808_: *mut leanh::LeanObject,
    mut v_a_5809_: *mut leanh::LeanObject,
    mut v_a_5810_: *mut leanh::LeanObject,
    mut v_a_5811_: *mut leanh::LeanObject,
    mut v_a_5812_: *mut leanh::LeanObject,
    mut v_a_5813_: *mut leanh::LeanObject,
    mut v_a_5814_: *mut leanh::LeanObject,
    mut v_a_5815_: *mut leanh::LeanObject,
    mut v_a_5816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5817_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_p_5804_, v_inst_5805_, v_fallback_5806_, v_a_5807_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_);
    leanh::lean_dec(v_a_5815_);
    leanh::lean_dec_ref(v_a_5814_);
    leanh::lean_dec(v_a_5813_);
    leanh::lean_dec_ref(v_a_5812_);
    leanh::lean_dec(v_a_5811_);
    leanh::lean_dec_ref(v_a_5810_);
    leanh::lean_dec(v_a_5809_);
    leanh::lean_dec_ref(v_a_5808_);
    leanh::lean_dec(v_a_5807_);
    return v_res_5817_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(
    mut v_p_5818_: *mut leanh::LeanObject,
    mut v_p_x27_5819_: *mut leanh::LeanObject,
    mut v_h_5820_: *mut leanh::LeanObject,
    mut v_inst_5821_: *mut leanh::LeanObject,
    mut v_inst_x27_5822_: *mut leanh::LeanObject,
    mut v_fallback_5823_: *mut leanh::LeanObject,
    mut v_a_5824_: *mut leanh::LeanObject,
    mut v_a_5825_: *mut leanh::LeanObject,
    mut v_a_5826_: *mut leanh::LeanObject,
    mut v_a_5827_: *mut leanh::LeanObject,
    mut v_a_5828_: *mut leanh::LeanObject,
    mut v_a_5829_: *mut leanh::LeanObject,
    mut v_a_5830_: *mut leanh::LeanObject,
    mut v_a_5831_: *mut leanh::LeanObject,
    mut v_a_5832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5836_: u8 = 0;
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5840_: u8 = 0;
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5848_: u8 = 0;
    let mut v_unused_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5850_: u8 = 0;
    let mut v_contextDependent_5851_: u8 = 0;
    let mut v_e_x27_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5853_: u8 = 0;
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5857_: u8 = 0;
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5860_: u8 = 0;
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5865_: u8 = 0;
    let mut v_unused_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_5867_: u8 = 0;
    let mut v_contextDependent_5868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_a_5832_);
                leanh::lean_inc_ref(v_a_5831_);
                leanh::lean_inc(v_a_5830_);
                leanh::lean_inc_ref(v_a_5829_);
                leanh::lean_inc(v_a_5828_);
                leanh::lean_inc_ref(v_a_5827_);
                leanh::lean_inc(v_a_5826_);
                leanh::lean_inc_ref(v_a_5825_);
                leanh::lean_inc(v_a_5824_);
                leanh::lean_inc_ref(v_inst_x27_5822_);
                v___x_5834_ = lean_sym_simp(
                    v_inst_x27_5822_,
                    v_a_5824_,
                    v_a_5825_,
                    v_a_5826_,
                    v_a_5827_,
                    v_a_5828_,
                    v_a_5829_,
                    v_a_5830_,
                    v_a_5831_,
                    v_a_5832_,
                );
                if leanh::lean_obj_tag(v___x_5834_) == 0 {
                    v_a_5835_ = leanh::lean_ctor_get(v___x_5834_, 0);
                    leanh::lean_inc(v_a_5835_);
                    leanh::lean_dec_ref_known(v___x_5834_, 1);
                    if leanh::lean_obj_tag(v_a_5835_) == 0 {
                        v_contextDependent_5836_ =
                            leanh::lean_ctor_get_uint8(v_a_5835_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_5835_, 0);
                        v___x_5837_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_5818_, v_p_x27_5819_, v_h_5820_, v_inst_5821_, v_inst_x27_5822_, v_fallback_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_, v_a_5830_, v_a_5831_, v_a_5832_);
                        if leanh::lean_obj_tag(v___x_5837_) == 0 {
                            v_a_5838_ = leanh::lean_ctor_get(v___x_5837_, 0);
                            leanh::lean_inc(v_a_5838_);
                            if v_contextDependent_5836_ == 0 {
                                leanh::lean_dec(v_a_5838_);
                                return v___x_5837_;
                            } else {
                                if leanh::lean_obj_tag(v_a_5838_) == 0 {
                                    v_contextDependent_5850_ =
                                        leanh::lean_ctor_get_uint8(v_a_5838_, 1 as u32);
                                    v___y_5840_ = v_contextDependent_5850_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_contextDependent_5851_ = leanh::lean_ctor_get_uint8(
                                        v_a_5838_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_5840_ = v_contextDependent_5851_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_5837_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_inst_x27_5822_);
                        v_e_x27_5852_ = leanh::lean_ctor_get(v_a_5835_, 0);
                        leanh::lean_inc_ref(v_e_x27_5852_);
                        v_contextDependent_5853_ = leanh::lean_ctor_get_uint8(
                            v_a_5835_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        leanh::lean_dec_ref_known(v_a_5835_, 2);
                        v___x_5854_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_matchDecideDecidableCongr(v_p_5818_, v_p_x27_5819_, v_h_5820_, v_inst_5821_, v_e_x27_5852_, v_fallback_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_, v_a_5830_, v_a_5831_, v_a_5832_);
                        if leanh::lean_obj_tag(v___x_5854_) == 0 {
                            v_a_5855_ = leanh::lean_ctor_get(v___x_5854_, 0);
                            leanh::lean_inc(v_a_5855_);
                            if v_contextDependent_5853_ == 0 {
                                leanh::lean_dec(v_a_5855_);
                                return v___x_5854_;
                            } else {
                                if leanh::lean_obj_tag(v_a_5855_) == 0 {
                                    v_contextDependent_5867_ =
                                        leanh::lean_ctor_get_uint8(v_a_5855_, 1 as u32);
                                    v___y_5857_ = v_contextDependent_5867_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_contextDependent_5868_ = leanh::lean_ctor_get_uint8(
                                        v_a_5855_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v___y_5857_ = v_contextDependent_5868_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_5854_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_fallback_5823_);
                    leanh::lean_dec_ref(v_inst_x27_5822_);
                    leanh::lean_dec_ref(v_inst_5821_);
                    leanh::lean_dec_ref(v_h_5820_);
                    leanh::lean_dec_ref(v_p_x27_5819_);
                    leanh::lean_dec_ref(v_p_5818_);
                    return v___x_5834_;
                }
            }
            1 => {
                if v___y_5840_ == 0 {
                    v_isSharedCheck_5848_ = (!leanh::lean_is_exclusive(v___x_5837_)) as u8;
                    if v_isSharedCheck_5848_ == 0 {
                        v_unused_5849_ = leanh::lean_ctor_get(v___x_5837_, 0);
                        leanh::lean_dec(v_unused_5849_);
                        v___x_5842_ = v___x_5837_;
                        v_isShared_5843_ = v_isSharedCheck_5848_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5837_);
                        v___x_5842_ = leanh::lean_box(0);
                        v_isShared_5843_ = v_isSharedCheck_5848_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5838_);
                    return v___x_5837_;
                }
            }
            2 => {
                v___x_5844_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_5838_);
                if v_isShared_5843_ == 0 {
                    leanh::lean_ctor_set(v___x_5842_, 0, v___x_5844_);
                    v___x_5846_ = v___x_5842_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5847_, 0, v___x_5844_);
                    v___x_5846_ = v_reuseFailAlloc_5847_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5846_;
            }
            4 => {
                if v___y_5857_ == 0 {
                    v_isSharedCheck_5865_ = (!leanh::lean_is_exclusive(v___x_5854_)) as u8;
                    if v_isSharedCheck_5865_ == 0 {
                        v_unused_5866_ = leanh::lean_ctor_get(v___x_5854_, 0);
                        leanh::lean_dec(v_unused_5866_);
                        v___x_5859_ = v___x_5854_;
                        v_isShared_5860_ = v_isSharedCheck_5865_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5854_);
                        v___x_5859_ = leanh::lean_box(0);
                        v_isShared_5860_ = v_isSharedCheck_5865_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5855_);
                    return v___x_5854_;
                }
            }
            5 => {
                v___x_5861_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_5855_);
                if v_isShared_5860_ == 0 {
                    leanh::lean_ctor_set(v___x_5859_, 0, v___x_5861_);
                    v___x_5863_ = v___x_5859_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5864_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5864_, 0, v___x_5861_);
                    v___x_5863_ = v_reuseFailAlloc_5864_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5863_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr___boxed(
    mut v_p_5869_: *mut leanh::LeanObject,
    mut v_p_x27_5870_: *mut leanh::LeanObject,
    mut v_h_5871_: *mut leanh::LeanObject,
    mut v_inst_5872_: *mut leanh::LeanObject,
    mut v_inst_x27_5873_: *mut leanh::LeanObject,
    mut v_fallback_5874_: *mut leanh::LeanObject,
    mut v_a_5875_: *mut leanh::LeanObject,
    mut v_a_5876_: *mut leanh::LeanObject,
    mut v_a_5877_: *mut leanh::LeanObject,
    mut v_a_5878_: *mut leanh::LeanObject,
    mut v_a_5879_: *mut leanh::LeanObject,
    mut v_a_5880_: *mut leanh::LeanObject,
    mut v_a_5881_: *mut leanh::LeanObject,
    mut v_a_5882_: *mut leanh::LeanObject,
    mut v_a_5883_: *mut leanh::LeanObject,
    mut v_a_5884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5885_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_p_5869_, v_p_x27_5870_, v_h_5871_, v_inst_5872_, v_inst_x27_5873_, v_fallback_5874_, v_a_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_, v_a_5883_);
    leanh::lean_dec(v_a_5883_);
    leanh::lean_dec_ref(v_a_5882_);
    leanh::lean_dec(v_a_5881_);
    leanh::lean_dec_ref(v_a_5880_);
    leanh::lean_dec(v_a_5879_);
    leanh::lean_dec_ref(v_a_5878_);
    leanh::lean_dec(v_a_5877_);
    leanh::lean_dec_ref(v_a_5876_);
    leanh::lean_dec(v_a_5875_);
    return v_res_5885_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(
    mut v___x_5887_: *mut leanh::LeanObject,
    mut v_e_x27_5888_: *mut leanh::LeanObject,
    mut v___y_5889_: *mut leanh::LeanObject,
    mut v___x_5890_: *mut leanh::LeanObject,
    mut v___x_5891_: *mut leanh::LeanObject,
    mut v___x_5892_: *mut leanh::LeanObject,
    mut v_arg_5893_: *mut leanh::LeanObject,
    mut v_proof_5894_: *mut leanh::LeanObject,
    mut v_arg_5895_: *mut leanh::LeanObject,
    mut v___x_5896_: u8,
    mut v_contextDependent_5897_: u8,
    mut v___y_5898_: *mut leanh::LeanObject,
    mut v___y_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
    mut v___y_5902_: *mut leanh::LeanObject,
    mut v___y_5903_: *mut leanh::LeanObject,
    mut v___y_5904_: *mut leanh::LeanObject,
    mut v___y_5905_: *mut leanh::LeanObject,
    mut v___y_5906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5914_: u8 = 0;
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5923_: u8 = 0;
    let mut v_a_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5927_: u8 = 0;
    let mut v___x_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5931_: u8 = 0;
    let mut v_a_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5935_: u8 = 0;
    let mut v___x_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5939_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5908_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_5887_, v___y_5902_);
                if leanh::lean_obj_tag(v___x_5908_) == 0 {
                    v_a_5909_ = leanh::lean_ctor_get(v___x_5908_, 0);
                    leanh::lean_inc(v_a_5909_);
                    leanh::lean_dec_ref_known(v___x_5908_, 1);
                    leanh::lean_inc_ref(v___y_5889_);
                    leanh::lean_inc_ref(v_e_x27_5888_);
                    v___x_5910_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___at___00Lean_Meta_Sym_Internal_mkAppS_u2083___at___00Lean_Meta_Sym_Internal_mkAppS_u2084___at___00__private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_spec__0_spec__0_spec__1(v_a_5909_, v_e_x27_5888_, v___y_5889_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_);
                    if leanh::lean_obj_tag(v___x_5910_) == 0 {
                        v_a_5911_ = leanh::lean_ctor_get(v___x_5910_, 0);
                        v_isSharedCheck_5923_ =
                            (!leanh::lean_is_exclusive(v___x_5910_)) as u8;
                        if v_isSharedCheck_5923_ == 0 {
                            v___x_5913_ = v___x_5910_;
                            v_isShared_5914_ = v_isSharedCheck_5923_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5911_);
                            leanh::lean_dec(v___x_5910_);
                            v___x_5913_ = leanh::lean_box(0);
                            v_isShared_5914_ = v_isSharedCheck_5923_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_arg_5895_);
                        leanh::lean_dec_ref(v_proof_5894_);
                        leanh::lean_dec_ref(v_arg_5893_);
                        leanh::lean_dec(v___x_5892_);
                        leanh::lean_dec_ref(v___x_5891_);
                        leanh::lean_dec_ref(v___x_5890_);
                        leanh::lean_dec_ref(v___y_5889_);
                        leanh::lean_dec_ref(v_e_x27_5888_);
                        v_a_5924_ = leanh::lean_ctor_get(v___x_5910_, 0);
                        v_isSharedCheck_5931_ =
                            (!leanh::lean_is_exclusive(v___x_5910_)) as u8;
                        if v_isSharedCheck_5931_ == 0 {
                            v___x_5926_ = v___x_5910_;
                            v_isShared_5927_ = v_isSharedCheck_5931_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5924_);
                            leanh::lean_dec(v___x_5910_);
                            v___x_5926_ = leanh::lean_box(0);
                            v_isShared_5927_ = v_isSharedCheck_5931_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_arg_5895_);
                    leanh::lean_dec_ref(v_proof_5894_);
                    leanh::lean_dec_ref(v_arg_5893_);
                    leanh::lean_dec(v___x_5892_);
                    leanh::lean_dec_ref(v___x_5891_);
                    leanh::lean_dec_ref(v___x_5890_);
                    leanh::lean_dec_ref(v___y_5889_);
                    leanh::lean_dec_ref(v_e_x27_5888_);
                    v_a_5932_ = leanh::lean_ctor_get(v___x_5908_, 0);
                    v_isSharedCheck_5939_ = (!leanh::lean_is_exclusive(v___x_5908_)) as u8;
                    if v_isSharedCheck_5939_ == 0 {
                        v___x_5934_ = v___x_5908_;
                        v_isShared_5935_ = v_isSharedCheck_5939_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5932_);
                        leanh::lean_dec(v___x_5908_);
                        v___x_5934_ = leanh::lean_box(0);
                        v_isShared_5935_ = v_isSharedCheck_5939_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5915_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___closed__0;
                v___x_5916_ = l_Lean_Name_mkStr3(v___x_5890_, v___x_5891_, v___x_5915_);
                v___x_5917_ = l_Lean_mkConst(v___x_5916_, v___x_5892_);
                v___x_5918_ = l_Lean_mkApp5(
                    v___x_5917_,
                    v_arg_5893_,
                    v_e_x27_5888_,
                    v_proof_5894_,
                    v_arg_5895_,
                    v___y_5889_,
                );
                v___x_5919_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_5919_, 0, v_a_5911_);
                leanh::lean_ctor_set(v___x_5919_, 1, v___x_5918_);
                leanh::lean_ctor_set_uint8(
                    v___x_5919_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5896_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_5919_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_5897_,
                );
                if v_isShared_5914_ == 0 {
                    leanh::lean_ctor_set(v___x_5913_, 0, v___x_5919_);
                    v___x_5921_ = v___x_5913_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5922_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5919_);
                    v___x_5921_ = v_reuseFailAlloc_5922_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5921_;
            }
            3 => {
                if v_isShared_5927_ == 0 {
                    v___x_5929_ = v___x_5926_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5930_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5924_);
                    v___x_5929_ = v_reuseFailAlloc_5930_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5929_;
            }
            5 => {
                if v_isShared_5935_ == 0 {
                    v___x_5937_ = v___x_5934_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5938_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_a_5932_);
                    v___x_5937_ = v_reuseFailAlloc_5938_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5937_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5940_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_e_x27_5941_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___y_5942_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_5943_: *mut leanh::LeanObject = *_args.add(3);
    let mut v___x_5944_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_5945_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_arg_5946_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_proof_5947_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_arg_5948_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___x_5949_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_contextDependent_5950_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5951_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5952_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5953_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5954_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5955_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5956_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5957_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_5958_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_5959_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_5960_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___x_23749__boxed_5961_: u8 = 0;
    let mut v_contextDependent_23750__boxed_5962_: u8 = 0;
    let mut v_res_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_23749__boxed_5961_ = (leanh::lean_unbox(v___x_5949_) as u8);
    v_contextDependent_23750__boxed_5962_ =
        (leanh::lean_unbox(v_contextDependent_5950_) as u8);
    v_res_5963_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1(
            v___x_5940_,
            v_e_x27_5941_,
            v___y_5942_,
            v___x_5943_,
            v___x_5944_,
            v___x_5945_,
            v_arg_5946_,
            v_proof_5947_,
            v_arg_5948_,
            v___x_23749__boxed_5961_,
            v_contextDependent_23750__boxed_5962_,
            v___y_5951_,
            v___y_5952_,
            v___y_5953_,
            v___y_5954_,
            v___y_5955_,
            v___y_5956_,
            v___y_5957_,
            v___y_5958_,
            v___y_5959_,
        );
    leanh::lean_dec(v___y_5959_);
    leanh::lean_dec_ref(v___y_5958_);
    leanh::lean_dec(v___y_5957_);
    leanh::lean_dec_ref(v___y_5956_);
    leanh::lean_dec(v___y_5955_);
    leanh::lean_dec_ref(v___y_5954_);
    leanh::lean_dec(v___y_5953_);
    leanh::lean_dec_ref(v___y_5952_);
    leanh::lean_dec(v___y_5951_);
    return v_res_5963_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5971_ = leanh::lean_box(0);
    v___x_5972_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__3;
    v___x_5973_ = l_Lean_mkConst(v___x_5972_, v___x_5971_);
    return v___x_5973_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5977_ = leanh::lean_box(0);
    v___x_5978_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__6;
    v___x_5979_ = l_Lean_mkConst(v___x_5978_, v___x_5977_);
    return v___x_5979_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5980_ = leanh::lean_box(0);
    v___x_5981_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1;
    v___x_5982_ = l_Lean_mkConst(v___x_5981_, v___x_5980_);
    return v___x_5982_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5988_ = leanh::lean_box(0);
    v___x_5989_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__10;
    v___x_5990_ = l_Lean_mkConst(v___x_5989_, v___x_5988_);
    return v___x_5990_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5996_ = leanh::lean_box(0);
    v___x_5997_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__13;
    v___x_5998_ = l_Lean_mkConst(v___x_5997_, v___x_5996_);
    return v___x_5998_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(
    mut v___x_5999_: u8,
    mut v_e_6000_: *mut leanh::LeanObject,
    mut v___y_6001_: *mut leanh::LeanObject,
    mut v___y_6002_: *mut leanh::LeanObject,
    mut v___y_6003_: *mut leanh::LeanObject,
    mut v___y_6004_: *mut leanh::LeanObject,
    mut v___y_6005_: *mut leanh::LeanObject,
    mut v___y_6006_: *mut leanh::LeanObject,
    mut v___y_6007_: *mut leanh::LeanObject,
    mut v___y_6008_: *mut leanh::LeanObject,
    mut v___y_6009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v_arg_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: u8 = 0;
    let mut v_arg_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: u8 = 0;
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_6027_: u8 = 0;
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: u8 = 0;
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: u8 = 0;
    let mut v___x_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6041_: u8 = 0;
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: u8 = 0;
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6049_: u8 = 0;
    let mut v_a_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6053_: u8 = 0;
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6057_: u8 = 0;
    let mut v_a_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6061_: u8 = 0;
    let mut v___x_6063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6065_: u8 = 0;
    let mut v___x_6066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6070_: u8 = 0;
    let mut v___x_6071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6077_: u8 = 0;
    let mut v_a_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6081_: u8 = 0;
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6085_: u8 = 0;
    let mut v_a_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6089_: u8 = 0;
    let mut v___x_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6093_: u8 = 0;
    let mut v_e_x27_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_6095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_6096_: u8 = 0;
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6099_: u8 = 0;
    let mut v___x_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: u8 = 0;
    let mut v___x_6103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: u8 = 0;
    let mut v___x_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6122_: u8 = 0;
    let mut v___x_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6126_: u8 = 0;
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6131_: u8 = 0;
    let mut v___x_6132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: u8 = 0;
    let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6141_: u8 = 0;
    let mut v_a_6142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6145_: u8 = 0;
    let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6149_: u8 = 0;
    let mut v_a_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6153_: u8 = 0;
    let mut v___x_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6157_: u8 = 0;
    let mut v___x_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6162_: u8 = 0;
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6171_: u8 = 0;
    let mut v_a_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6175_: u8 = 0;
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6179_: u8 = 0;
    let mut v_a_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6183_: u8 = 0;
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6187_: u8 = 0;
    let mut v_isSharedCheck_6188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6014_ = l_Lean_Expr_cleanupAnnotations(v_e_6000_);
                v___x_6015_ = l_Lean_Expr_isApp(v___x_6014_);
                if v___x_6015_ == 0 {
                    leanh::lean_dec_ref(v___x_6014_);
                    state = 1;
                    continue;
                } else {
                    v_arg_6016_ = leanh::lean_ctor_get(v___x_6014_, 1);
                    leanh::lean_inc_ref(v_arg_6016_);
                    v___x_6017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6014_);
                    v___x_6018_ = l_Lean_Expr_isApp(v___x_6017_);
                    if v___x_6018_ == 0 {
                        leanh::lean_dec_ref(v___x_6017_);
                        leanh::lean_dec_ref(v_arg_6016_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_6019_ = leanh::lean_ctor_get(v___x_6017_, 1);
                        leanh::lean_inc_ref(v_arg_6019_);
                        v___x_6020_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6017_);
                        v___x_6021_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance___closed__0;
                        v___x_6022_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__0;
                        v___x_6023_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__1;
                        v___x_6024_ = l_Lean_Expr_isConstOf(v___x_6020_, v___x_6023_);
                        leanh::lean_dec_ref(v___x_6020_);
                        if v___x_6024_ == 0 {
                            leanh::lean_dec_ref(v_arg_6019_);
                            leanh::lean_dec_ref(v_arg_6016_);
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v___y_6009_);
                            leanh::lean_inc_ref(v___y_6008_);
                            leanh::lean_inc(v___y_6007_);
                            leanh::lean_inc_ref(v___y_6006_);
                            leanh::lean_inc(v___y_6005_);
                            leanh::lean_inc_ref(v___y_6004_);
                            leanh::lean_inc(v___y_6003_);
                            leanh::lean_inc_ref(v___y_6002_);
                            leanh::lean_inc(v___y_6001_);
                            leanh::lean_inc_ref(v_arg_6019_);
                            v___x_6025_ = lean_sym_simp(
                                v_arg_6019_,
                                v___y_6001_,
                                v___y_6002_,
                                v___y_6003_,
                                v___y_6004_,
                                v___y_6005_,
                                v___y_6006_,
                                v___y_6007_,
                                v___y_6008_,
                                v___y_6009_,
                            );
                            if leanh::lean_obj_tag(v___x_6025_) == 0 {
                                v_a_6026_ = leanh::lean_ctor_get(v___x_6025_, 0);
                                leanh::lean_inc(v_a_6026_);
                                leanh::lean_dec_ref_known(v___x_6025_, 1);
                                if leanh::lean_obj_tag(v_a_6026_) == 0 {
                                    v_contextDependent_6027_ =
                                        leanh::lean_ctor_get_uint8(v_a_6026_, 1 as u32);
                                    leanh::lean_dec_ref_known(v_a_6026_, 0);
                                    v___x_6028_ = l_Lean_Meta_Sym_isTrueExpr___redArg(
                                        v_arg_6019_,
                                        v___y_6004_,
                                    );
                                    if leanh::lean_obj_tag(v___x_6028_) == 0 {
                                        v_a_6029_ = leanh::lean_ctor_get(v___x_6028_, 0);
                                        leanh::lean_inc(v_a_6029_);
                                        leanh::lean_dec_ref_known(v___x_6028_, 1);
                                        v___x_6030_ = (leanh::lean_unbox(v_a_6029_) as u8);
                                        if v___x_6030_ == 0 {
                                            v___x_6031_ = l_Lean_Meta_Sym_isFalseExpr___redArg(
                                                v_arg_6019_,
                                                v___y_6004_,
                                            );
                                            if leanh::lean_obj_tag(v___x_6031_) == 0 {
                                                v_a_6032_ =
                                                    leanh::lean_ctor_get(v___x_6031_, 0);
                                                leanh::lean_inc(v_a_6032_);
                                                leanh::lean_dec_ref_known(v___x_6031_, 1);
                                                v___x_6033_ =
                                                    (leanh::lean_unbox(v_a_6032_) as u8);
                                                leanh::lean_dec(v_a_6032_);
                                                if v___x_6033_ == 0 {
                                                    leanh::lean_dec(v_a_6029_);
                                                    v___x_6034_ = l_Lean_Meta_Sym_Simp_mkRflResult(
                                                        v___x_6024_,
                                                        v_contextDependent_6027_,
                                                    );
                                                    v___f_6035_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__0___boxed as *mut core::ffi::c_void, 11, 1);
                                                    leanh::lean_closure_set(
                                                        v___f_6035_,
                                                        0,
                                                        v___x_6034_,
                                                    );
                                                    v___x_6036_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidable(v_arg_6019_, v_arg_6016_, v___f_6035_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
                                                    return v___x_6036_;
                                                } else {
                                                    leanh::lean_dec_ref(v_arg_6019_);
                                                    v___x_6037_ =
                                                        l_Lean_Meta_Sym_getBoolFalseExpr___redArg(
                                                            v___y_6004_,
                                                        );
                                                    if leanh::lean_obj_tag(v___x_6037_) == 0
                                                    {
                                                        v_a_6038_ = leanh::lean_ctor_get(
                                                            v___x_6037_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_6049_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_6037_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_6049_ == 0 {
                                                            v___x_6040_ = v___x_6037_;
                                                            v_isShared_6041_ =
                                                                v_isSharedCheck_6049_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_6038_);
                                                            leanh::lean_dec(v___x_6037_);
                                                            v___x_6040_ = leanh::lean_box(0);
                                                            v_isShared_6041_ =
                                                                v_isSharedCheck_6049_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        leanh::lean_dec(v_a_6029_);
                                                        leanh::lean_dec_ref(v_arg_6016_);
                                                        v_a_6050_ = leanh::lean_ctor_get(
                                                            v___x_6037_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_6057_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_6037_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_6057_ == 0 {
                                                            v___x_6052_ = v___x_6037_;
                                                            v_isShared_6053_ =
                                                                v_isSharedCheck_6057_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_6050_);
                                                            leanh::lean_dec(v___x_6037_);
                                                            v___x_6052_ = leanh::lean_box(0);
                                                            v_isShared_6053_ =
                                                                v_isSharedCheck_6057_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec(v_a_6029_);
                                                leanh::lean_dec_ref(v_arg_6019_);
                                                leanh::lean_dec_ref(v_arg_6016_);
                                                v_a_6058_ =
                                                    leanh::lean_ctor_get(v___x_6031_, 0);
                                                v_isSharedCheck_6065_ =
                                                    (!leanh::lean_is_exclusive(v___x_6031_))
                                                        as u8;
                                                if v_isSharedCheck_6065_ == 0 {
                                                    v___x_6060_ = v___x_6031_;
                                                    v_isShared_6061_ = v_isSharedCheck_6065_;
                                                    state = 6;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_6058_);
                                                    leanh::lean_dec(v___x_6031_);
                                                    v___x_6060_ = leanh::lean_box(0);
                                                    v_isShared_6061_ = v_isSharedCheck_6065_;
                                                    state = 6;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_a_6029_);
                                            leanh::lean_dec_ref(v_arg_6019_);
                                            v___x_6066_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(
                                                v___y_6004_,
                                            );
                                            if leanh::lean_obj_tag(v___x_6066_) == 0 {
                                                v_a_6067_ =
                                                    leanh::lean_ctor_get(v___x_6066_, 0);
                                                v_isSharedCheck_6077_ =
                                                    (!leanh::lean_is_exclusive(v___x_6066_))
                                                        as u8;
                                                if v_isSharedCheck_6077_ == 0 {
                                                    v___x_6069_ = v___x_6066_;
                                                    v_isShared_6070_ = v_isSharedCheck_6077_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_6067_);
                                                    leanh::lean_dec(v___x_6066_);
                                                    v___x_6069_ = leanh::lean_box(0);
                                                    v_isShared_6070_ = v_isSharedCheck_6077_;
                                                    state = 8;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v_arg_6016_);
                                                v_a_6078_ =
                                                    leanh::lean_ctor_get(v___x_6066_, 0);
                                                v_isSharedCheck_6085_ =
                                                    (!leanh::lean_is_exclusive(v___x_6066_))
                                                        as u8;
                                                if v_isSharedCheck_6085_ == 0 {
                                                    v___x_6080_ = v___x_6066_;
                                                    v_isShared_6081_ = v_isSharedCheck_6085_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_6078_);
                                                    leanh::lean_dec(v___x_6066_);
                                                    v___x_6080_ = leanh::lean_box(0);
                                                    v_isShared_6081_ = v_isSharedCheck_6085_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_arg_6019_);
                                        leanh::lean_dec_ref(v_arg_6016_);
                                        v_a_6086_ = leanh::lean_ctor_get(v___x_6028_, 0);
                                        v_isSharedCheck_6093_ =
                                            (!leanh::lean_is_exclusive(v___x_6028_)) as u8;
                                        if v_isSharedCheck_6093_ == 0 {
                                            v___x_6088_ = v___x_6028_;
                                            v_isShared_6089_ = v_isSharedCheck_6093_;
                                            state = 12;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6086_);
                                            leanh::lean_dec(v___x_6028_);
                                            v___x_6088_ = leanh::lean_box(0);
                                            v_isShared_6089_ = v_isSharedCheck_6093_;
                                            state = 12;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_e_x27_6094_ = leanh::lean_ctor_get(v_a_6026_, 0);
                                    v_proof_6095_ = leanh::lean_ctor_get(v_a_6026_, 1);
                                    v_contextDependent_6096_ = leanh::lean_ctor_get_uint8(
                                        v_a_6026_,
                                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2
                                            + 1) as u32,
                                    );
                                    v_isSharedCheck_6188_ =
                                        (!leanh::lean_is_exclusive(v_a_6026_)) as u8;
                                    if v_isSharedCheck_6188_ == 0 {
                                        v___x_6098_ = v_a_6026_;
                                        v_isShared_6099_ = v_isSharedCheck_6188_;
                                        state = 14;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_proof_6095_);
                                        leanh::lean_inc(v_e_x27_6094_);
                                        leanh::lean_dec(v_a_6026_);
                                        v___x_6098_ = leanh::lean_box(0);
                                        v_isShared_6099_ = v_isSharedCheck_6188_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_arg_6019_);
                                leanh::lean_dec_ref(v_arg_6016_);
                                return v___x_6025_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6012_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                leanh::lean_ctor_set_uint8(v___x_6012_, 0 as u32, v___x_5999_);
                leanh::lean_ctor_set_uint8(v___x_6012_, 1 as u32, v___x_5999_);
                v___x_6013_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6013_, 0, v___x_6012_);
                return v___x_6013_;
            }
            2 => {
                v___x_6042_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__4);
                v___x_6043_ = l_Lean_Expr_app___override(v___x_6042_, v_arg_6016_);
                v___x_6044_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_6044_, 0, v_a_6038_);
                leanh::lean_ctor_set(v___x_6044_, 1, v___x_6043_);
                v___x_6045_ = (leanh::lean_unbox(v_a_6029_) as u8);
                leanh::lean_dec(v_a_6029_);
                leanh::lean_ctor_set_uint8(
                    v___x_6044_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_6045_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6044_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_6027_,
                );
                if v_isShared_6041_ == 0 {
                    leanh::lean_ctor_set(v___x_6040_, 0, v___x_6044_);
                    v___x_6047_ = v___x_6040_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6048_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 0, v___x_6044_);
                    v___x_6047_ = v_reuseFailAlloc_6048_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6047_;
            }
            4 => {
                if v_isShared_6053_ == 0 {
                    v___x_6055_ = v___x_6052_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6056_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
                    v___x_6055_ = v_reuseFailAlloc_6056_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6055_;
            }
            6 => {
                if v_isShared_6061_ == 0 {
                    v___x_6063_ = v___x_6060_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6064_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_a_6058_);
                    v___x_6063_ = v_reuseFailAlloc_6064_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6063_;
            }
            8 => {
                v___x_6071_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__7);
                v___x_6072_ = l_Lean_Expr_app___override(v___x_6071_, v_arg_6016_);
                v___x_6073_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_6073_, 0, v_a_6067_);
                leanh::lean_ctor_set(v___x_6073_, 1, v___x_6072_);
                leanh::lean_ctor_set_uint8(
                    v___x_6073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5999_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6073_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_6027_,
                );
                if v_isShared_6070_ == 0 {
                    leanh::lean_ctor_set(v___x_6069_, 0, v___x_6073_);
                    v___x_6075_ = v___x_6069_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6076_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6076_, 0, v___x_6073_);
                    v___x_6075_ = v_reuseFailAlloc_6076_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6075_;
            }
            10 => {
                if v_isShared_6081_ == 0 {
                    v___x_6083_ = v___x_6080_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6084_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6084_, 0, v_a_6078_);
                    v___x_6083_ = v_reuseFailAlloc_6084_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6083_;
            }
            12 => {
                if v_isShared_6089_ == 0 {
                    v___x_6091_ = v___x_6088_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6092_, 0, v_a_6086_);
                    v___x_6091_ = v_reuseFailAlloc_6092_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6091_;
            }
            14 => {
                v___x_6100_ = l_Lean_Meta_Sym_isTrueExpr___redArg(v_e_x27_6094_, v___y_6004_);
                if leanh::lean_obj_tag(v___x_6100_) == 0 {
                    v_a_6101_ = leanh::lean_ctor_get(v___x_6100_, 0);
                    leanh::lean_inc(v_a_6101_);
                    leanh::lean_dec_ref_known(v___x_6100_, 1);
                    v___x_6102_ = (leanh::lean_unbox(v_a_6101_) as u8);
                    if v___x_6102_ == 0 {
                        v___x_6103_ =
                            l_Lean_Meta_Sym_isFalseExpr___redArg(v_e_x27_6094_, v___y_6004_);
                        if leanh::lean_obj_tag(v___x_6103_) == 0 {
                            v_a_6104_ = leanh::lean_ctor_get(v___x_6103_, 0);
                            leanh::lean_inc(v_a_6104_);
                            leanh::lean_dec_ref_known(v___x_6103_, 1);
                            v___x_6105_ = (leanh::lean_unbox(v_a_6104_) as u8);
                            leanh::lean_dec(v_a_6104_);
                            if v___x_6105_ == 0 {
                                leanh::lean_dec(v_a_6101_);
                                leanh::lean_del_object(v___x_6098_);
                                leanh::lean_inc_ref(v_e_x27_6094_);
                                v___x_6106_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_trySynthComputableInstance(v_e_x27_6094_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
                                if leanh::lean_obj_tag(v___x_6106_) == 0 {
                                    v_a_6107_ = leanh::lean_ctor_get(v___x_6106_, 0);
                                    leanh::lean_inc(v_a_6107_);
                                    leanh::lean_dec_ref_known(v___x_6106_, 1);
                                    if leanh::lean_obj_tag(v_a_6107_) == 0 {
                                        v___x_6116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___lam__2___closed__6);
                                        leanh::lean_inc_ref(v_proof_6095_);
                                        leanh::lean_inc_ref(v_arg_6016_);
                                        leanh::lean_inc_ref(v_e_x27_6094_);
                                        leanh::lean_inc_ref(v_arg_6019_);
                                        v___x_6117_ = l_Lean_mkApp4(
                                            v___x_6116_,
                                            v_arg_6019_,
                                            v_e_x27_6094_,
                                            v_arg_6016_,
                                            v_proof_6095_,
                                        );
                                        v___y_6109_ = v___x_6117_;
                                        state = 15;
                                        continue;
                                    } else {
                                        v_val_6118_ = leanh::lean_ctor_get(v_a_6107_, 0);
                                        leanh::lean_inc(v_val_6118_);
                                        leanh::lean_dec_ref_known(v_a_6107_, 1);
                                        v___y_6109_ = v_val_6118_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_proof_6095_);
                                    leanh::lean_dec_ref(v_e_x27_6094_);
                                    leanh::lean_dec_ref(v_arg_6019_);
                                    leanh::lean_dec_ref(v_arg_6016_);
                                    v_a_6119_ = leanh::lean_ctor_get(v___x_6106_, 0);
                                    v_isSharedCheck_6126_ =
                                        (!leanh::lean_is_exclusive(v___x_6106_)) as u8;
                                    if v_isSharedCheck_6126_ == 0 {
                                        v___x_6121_ = v___x_6106_;
                                        v_isShared_6122_ = v_isSharedCheck_6126_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6119_);
                                        leanh::lean_dec(v___x_6106_);
                                        v___x_6121_ = leanh::lean_box(0);
                                        v_isShared_6122_ = v_isSharedCheck_6126_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v_e_x27_6094_);
                                v___x_6127_ =
                                    l_Lean_Meta_Sym_getBoolFalseExpr___redArg(v___y_6004_);
                                if leanh::lean_obj_tag(v___x_6127_) == 0 {
                                    v_a_6128_ = leanh::lean_ctor_get(v___x_6127_, 0);
                                    v_isSharedCheck_6141_ =
                                        (!leanh::lean_is_exclusive(v___x_6127_)) as u8;
                                    if v_isSharedCheck_6141_ == 0 {
                                        v___x_6130_ = v___x_6127_;
                                        v_isShared_6131_ = v_isSharedCheck_6141_;
                                        state = 18;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6128_);
                                        leanh::lean_dec(v___x_6127_);
                                        v___x_6130_ = leanh::lean_box(0);
                                        v_isShared_6131_ = v_isSharedCheck_6141_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_a_6101_);
                                    leanh::lean_del_object(v___x_6098_);
                                    leanh::lean_dec_ref(v_proof_6095_);
                                    leanh::lean_dec_ref(v_arg_6019_);
                                    leanh::lean_dec_ref(v_arg_6016_);
                                    v_a_6142_ = leanh::lean_ctor_get(v___x_6127_, 0);
                                    v_isSharedCheck_6149_ =
                                        (!leanh::lean_is_exclusive(v___x_6127_)) as u8;
                                    if v_isSharedCheck_6149_ == 0 {
                                        v___x_6144_ = v___x_6127_;
                                        v_isShared_6145_ = v_isSharedCheck_6149_;
                                        state = 21;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_6142_);
                                        leanh::lean_dec(v___x_6127_);
                                        v___x_6144_ = leanh::lean_box(0);
                                        v_isShared_6145_ = v_isSharedCheck_6149_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_6101_);
                            leanh::lean_del_object(v___x_6098_);
                            leanh::lean_dec_ref(v_proof_6095_);
                            leanh::lean_dec_ref(v_e_x27_6094_);
                            leanh::lean_dec_ref(v_arg_6019_);
                            leanh::lean_dec_ref(v_arg_6016_);
                            v_a_6150_ = leanh::lean_ctor_get(v___x_6103_, 0);
                            v_isSharedCheck_6157_ =
                                (!leanh::lean_is_exclusive(v___x_6103_)) as u8;
                            if v_isSharedCheck_6157_ == 0 {
                                v___x_6152_ = v___x_6103_;
                                v_isShared_6153_ = v_isSharedCheck_6157_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6150_);
                                leanh::lean_dec(v___x_6103_);
                                v___x_6152_ = leanh::lean_box(0);
                                v_isShared_6153_ = v_isSharedCheck_6157_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_6101_);
                        leanh::lean_dec_ref(v_e_x27_6094_);
                        v___x_6158_ = l_Lean_Meta_Sym_getBoolTrueExpr___redArg(v___y_6004_);
                        if leanh::lean_obj_tag(v___x_6158_) == 0 {
                            v_a_6159_ = leanh::lean_ctor_get(v___x_6158_, 0);
                            v_isSharedCheck_6171_ =
                                (!leanh::lean_is_exclusive(v___x_6158_)) as u8;
                            if v_isSharedCheck_6171_ == 0 {
                                v___x_6161_ = v___x_6158_;
                                v_isShared_6162_ = v_isSharedCheck_6171_;
                                state = 25;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6159_);
                                leanh::lean_dec(v___x_6158_);
                                v___x_6161_ = leanh::lean_box(0);
                                v_isShared_6162_ = v_isSharedCheck_6171_;
                                state = 25;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6098_);
                            leanh::lean_dec_ref(v_proof_6095_);
                            leanh::lean_dec_ref(v_arg_6019_);
                            leanh::lean_dec_ref(v_arg_6016_);
                            v_a_6172_ = leanh::lean_ctor_get(v___x_6158_, 0);
                            v_isSharedCheck_6179_ =
                                (!leanh::lean_is_exclusive(v___x_6158_)) as u8;
                            if v_isSharedCheck_6179_ == 0 {
                                v___x_6174_ = v___x_6158_;
                                v_isShared_6175_ = v_isSharedCheck_6179_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6172_);
                                leanh::lean_dec(v___x_6158_);
                                v___x_6174_ = leanh::lean_box(0);
                                v_isShared_6175_ = v_isSharedCheck_6179_;
                                state = 28;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_6098_);
                    leanh::lean_dec_ref(v_proof_6095_);
                    leanh::lean_dec_ref(v_e_x27_6094_);
                    leanh::lean_dec_ref(v_arg_6019_);
                    leanh::lean_dec_ref(v_arg_6016_);
                    v_a_6180_ = leanh::lean_ctor_get(v___x_6100_, 0);
                    v_isSharedCheck_6187_ = (!leanh::lean_is_exclusive(v___x_6100_)) as u8;
                    if v_isSharedCheck_6187_ == 0 {
                        v___x_6182_ = v___x_6100_;
                        v_isShared_6183_ = v_isSharedCheck_6187_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6180_);
                        leanh::lean_dec(v___x_6100_);
                        v___x_6182_ = leanh::lean_box(0);
                        v_isShared_6183_ = v_isSharedCheck_6187_;
                        state = 30;
                        continue;
                    }
                }
            }
            15 => {
                v___x_6110_ = leanh::lean_box(0);
                v___x_6111_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__8);
                v___x_6112_ = leanh::lean_box((v___x_6024_) as usize);
                v___x_6113_ = leanh::lean_box((v_contextDependent_6096_) as usize);
                leanh::lean_inc_ref(v_arg_6016_);
                leanh::lean_inc_ref(v_proof_6095_);
                leanh::lean_inc_ref(v_arg_6019_);
                leanh::lean_inc_ref(v___y_6109_);
                leanh::lean_inc_ref(v_e_x27_6094_);
                v___f_6114_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__1___boxed as *mut core::ffi::c_void, 21, 11);
                leanh::lean_closure_set(v___f_6114_, 0, v___x_6111_);
                leanh::lean_closure_set(v___f_6114_, 1, v_e_x27_6094_);
                leanh::lean_closure_set(v___f_6114_, 2, v___y_6109_);
                leanh::lean_closure_set(v___f_6114_, 3, v___x_6021_);
                leanh::lean_closure_set(v___f_6114_, 4, v___x_6022_);
                leanh::lean_closure_set(v___f_6114_, 5, v___x_6110_);
                leanh::lean_closure_set(v___f_6114_, 6, v_arg_6019_);
                leanh::lean_closure_set(v___f_6114_, 7, v_proof_6095_);
                leanh::lean_closure_set(v___f_6114_, 8, v_arg_6016_);
                leanh::lean_closure_set(v___f_6114_, 9, v___x_6112_);
                leanh::lean_closure_set(v___f_6114_, 10, v___x_6113_);
                v___x_6115_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpAndMatchDecideDecidableCongr(v_arg_6019_, v_e_x27_6094_, v_proof_6095_, v_arg_6016_, v___y_6109_, v___f_6114_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
                return v___x_6115_;
            }
            16 => {
                if v_isShared_6122_ == 0 {
                    v___x_6124_ = v___x_6121_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6125_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_a_6119_);
                    v___x_6124_ = v_reuseFailAlloc_6125_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6124_;
            }
            18 => {
                v___x_6132_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__11);
                v___x_6133_ = l_Lean_mkApp3(v___x_6132_, v_arg_6019_, v_arg_6016_, v_proof_6095_);
                if v_isShared_6099_ == 0 {
                    leanh::lean_ctor_set(v___x_6098_, 1, v___x_6133_);
                    leanh::lean_ctor_set(v___x_6098_, 0, v_a_6128_);
                    v___x_6135_ = v___x_6098_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6140_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6140_, 0, v_a_6128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6140_, 1, v___x_6133_);
                    v___x_6135_ = v_reuseFailAlloc_6140_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_6136_ = (leanh::lean_unbox(v_a_6101_) as u8);
                leanh::lean_dec(v_a_6101_);
                leanh::lean_ctor_set_uint8(
                    v___x_6135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_6136_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6135_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v_contextDependent_6096_,
                );
                if v_isShared_6131_ == 0 {
                    leanh::lean_ctor_set(v___x_6130_, 0, v___x_6135_);
                    v___x_6138_ = v___x_6130_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6139_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6139_, 0, v___x_6135_);
                    v___x_6138_ = v_reuseFailAlloc_6139_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6138_;
            }
            21 => {
                if v_isShared_6145_ == 0 {
                    v___x_6147_ = v___x_6144_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6148_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6148_, 0, v_a_6142_);
                    v___x_6147_ = v_reuseFailAlloc_6148_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6147_;
            }
            23 => {
                if v_isShared_6153_ == 0 {
                    v___x_6155_ = v___x_6152_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6150_);
                    v___x_6155_ = v_reuseFailAlloc_6156_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6155_;
            }
            25 => {
                v___x_6163_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14_once), _init_l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___closed__14);
                v___x_6164_ = l_Lean_mkApp3(v___x_6163_, v_arg_6019_, v_arg_6016_, v_proof_6095_);
                if v_isShared_6099_ == 0 {
                    leanh::lean_ctor_set(v___x_6098_, 1, v___x_6164_);
                    leanh::lean_ctor_set(v___x_6098_, 0, v_a_6159_);
                    v___x_6166_ = v___x_6098_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6170_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6170_, 0, v_a_6159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6170_, 1, v___x_6164_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6170_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        v_contextDependent_6096_,
                    );
                    v___x_6166_ = v_reuseFailAlloc_6170_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                leanh::lean_ctor_set_uint8(
                    v___x_6166_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_5999_,
                );
                if v_isShared_6162_ == 0 {
                    leanh::lean_ctor_set(v___x_6161_, 0, v___x_6166_);
                    v___x_6168_ = v___x_6161_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_6169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6169_, 0, v___x_6166_);
                    v___x_6168_ = v_reuseFailAlloc_6169_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_6168_;
            }
            28 => {
                if v_isShared_6175_ == 0 {
                    v___x_6177_ = v___x_6174_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_6178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6178_, 0, v_a_6172_);
                    v___x_6177_ = v_reuseFailAlloc_6178_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_6177_;
            }
            30 => {
                if v_isShared_6183_ == 0 {
                    v___x_6185_ = v___x_6182_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_6186_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_a_6180_);
                    v___x_6185_ = v_reuseFailAlloc_6186_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_6185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed(
    mut v___x_6189_: *mut leanh::LeanObject,
    mut v_e_6190_: *mut leanh::LeanObject,
    mut v___y_6191_: *mut leanh::LeanObject,
    mut v___y_6192_: *mut leanh::LeanObject,
    mut v___y_6193_: *mut leanh::LeanObject,
    mut v___y_6194_: *mut leanh::LeanObject,
    mut v___y_6195_: *mut leanh::LeanObject,
    mut v___y_6196_: *mut leanh::LeanObject,
    mut v___y_6197_: *mut leanh::LeanObject,
    mut v___y_6198_: *mut leanh::LeanObject,
    mut v___y_6199_: *mut leanh::LeanObject,
    mut v___y_6200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_23949__boxed_6201_: u8 = 0;
    let mut v_res_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_23949__boxed_6201_ = (leanh::lean_unbox(v___x_6189_) as u8);
    v_res_6202_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0(
            v___x_23949__boxed_6201_,
            v_e_6190_,
            v___y_6191_,
            v___y_6192_,
            v___y_6193_,
            v___y_6194_,
            v___y_6195_,
            v___y_6196_,
            v___y_6197_,
            v___y_6198_,
            v___y_6199_,
        );
    leanh::lean_dec(v___y_6199_);
    leanh::lean_dec_ref(v___y_6198_);
    leanh::lean_dec(v___y_6197_);
    leanh::lean_dec_ref(v___y_6196_);
    leanh::lean_dec(v___y_6195_);
    leanh::lean_dec_ref(v___y_6194_);
    leanh::lean_dec(v___y_6193_);
    leanh::lean_dec_ref(v___y_6192_);
    leanh::lean_dec(v___y_6191_);
    return v_res_6202_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(
    mut v_e_6203_: *mut leanh::LeanObject,
    mut v_a_6204_: *mut leanh::LeanObject,
    mut v_a_6205_: *mut leanh::LeanObject,
    mut v_a_6206_: *mut leanh::LeanObject,
    mut v_a_6207_: *mut leanh::LeanObject,
    mut v_a_6208_: *mut leanh::LeanObject,
    mut v_a_6209_: *mut leanh::LeanObject,
    mut v_a_6210_: *mut leanh::LeanObject,
    mut v_a_6211_: *mut leanh::LeanObject,
    mut v_a_6212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numArgs_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6216_: u8 = 0;
    v_numArgs_6214_ = l_Lean_Expr_getAppNumArgs(v_e_6203_);
    v___x_6215_ = leanh::lean_unsigned_to_nat(2);
    v___x_6216_ = lean_nat_dec_lt(v_numArgs_6214_, v___x_6215_);
    if v___x_6216_ == 0 {
        let mut v___x_6217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6217_ = leanh::lean_box((v___x_6216_) as usize);
        v___f_6218_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___lam__0___boxed as *mut core::ffi::c_void, 12, 1);
        leanh::lean_closure_set(v___f_6218_, 0, v___x_6217_);
        v___x_6219_ = lean_nat_sub(v_numArgs_6214_, v___x_6215_);
        leanh::lean_dec(v_numArgs_6214_);
        v___x_6220_ = l_Lean_Meta_Sym_Simp_propagateOverApplied(
            v_e_6203_,
            v___x_6219_,
            v___f_6218_,
            v_a_6204_,
            v_a_6205_,
            v_a_6206_,
            v_a_6207_,
            v_a_6208_,
            v_a_6209_,
            v_a_6210_,
            v_a_6211_,
            v_a_6212_,
        );
        leanh::lean_dec(v___x_6219_);
        return v___x_6220_;
    } else {
        let mut v___x_6221_: u8 = 0;
        let mut v___x_6222_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6223_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_numArgs_6214_);
        leanh::lean_dec_ref(v_e_6203_);
        v___x_6221_ = 0;
        v___x_6222_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
        leanh::lean_ctor_set_uint8(v___x_6222_, 0 as u32, v___x_6216_);
        leanh::lean_ctor_set_uint8(v___x_6222_, 1 as u32, v___x_6221_);
        v___x_6223_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6223_, 0, v___x_6222_);
        return v___x_6223_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed(
    mut v_e_6224_: *mut leanh::LeanObject,
    mut v_a_6225_: *mut leanh::LeanObject,
    mut v_a_6226_: *mut leanh::LeanObject,
    mut v_a_6227_: *mut leanh::LeanObject,
    mut v_a_6228_: *mut leanh::LeanObject,
    mut v_a_6229_: *mut leanh::LeanObject,
    mut v_a_6230_: *mut leanh::LeanObject,
    mut v_a_6231_: *mut leanh::LeanObject,
    mut v_a_6232_: *mut leanh::LeanObject,
    mut v_a_6233_: *mut leanh::LeanObject,
    mut v_a_6234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6235_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv(
        v_e_6224_, v_a_6225_, v_a_6226_, v_a_6227_, v_a_6228_, v_a_6229_, v_a_6230_, v_a_6231_,
        v_a_6232_, v_a_6233_,
    );
    leanh::lean_dec(v_a_6233_);
    leanh::lean_dec_ref(v_a_6232_);
    leanh::lean_dec(v_a_6231_);
    leanh::lean_dec_ref(v_a_6230_);
    leanh::lean_dec(v_a_6229_);
    leanh::lean_dec_ref(v_a_6228_);
    leanh::lean_dec(v_a_6227_);
    leanh::lean_dec_ref(v_a_6226_);
    leanh::lean_dec(v_a_6225_);
    return v_res_6235_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_()
-> *mut leanh::LeanObject {
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6251_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_;
    v___x_6252_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__3_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_;
    v___x_6253_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed
            as *mut core::ffi::c_void,
        11,
        0,
    );
    v___x_6254_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_6251_, v___x_6252_, v___x_6253_);
    return v___x_6254_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13____boxed(
    mut v_a_6255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6256_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_();
    return v_res_6256_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___x_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: u8 = 0;
    let mut v___x_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6258_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_;
    v___x_6259_ = 0;
    v___x_6260_ = leanh::lean_alloc_closure(
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___boxed
            as *mut core::ffi::c_void,
        11,
        0,
    );
    v___x_6261_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_6258_, v___x_6259_, v___x_6260_);
    return v___x_6261_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15____boxed(
    mut v_a_6262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6263_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_();
    return v_res_6263_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(
    mut v_declName_6264_: *mut leanh::LeanObject,
    mut v___y_6265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: u8 = 0;
    let mut v___x_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6267_ = lean_st_ref_get(v___y_6265_);
    v_env_6268_ = leanh::lean_ctor_get(v___x_6267_, 0);
    leanh::lean_inc_ref(v_env_6268_);
    leanh::lean_dec(v___x_6267_);
    v___x_6269_ = lean_get_reducibility_status(v_env_6268_, v_declName_6264_);
    v___x_6270_ = leanh::lean_box((v___x_6269_) as usize);
    v___x_6271_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6271_, 0, v___x_6270_);
    return v___x_6271_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg___boxed(
    mut v_declName_6272_: *mut leanh::LeanObject,
    mut v___y_6273_: *mut leanh::LeanObject,
    mut v___y_6274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6275_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_6272_, v___y_6273_);
    leanh::lean_dec(v___y_6273_);
    return v_res_6275_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(
    mut v_declName_6276_: *mut leanh::LeanObject,
    mut v___y_6277_: *mut leanh::LeanObject,
    mut v___y_6278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6280_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_6276_, v___y_6278_);
    return v___x_6280_;
}
pub unsafe fn l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___boxed(
    mut v_declName_6281_: *mut leanh::LeanObject,
    mut v___y_6282_: *mut leanh::LeanObject,
    mut v___y_6283_: *mut leanh::LeanObject,
    mut v___y_6284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6285_ =
        l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1(
            v_declName_6281_,
            v___y_6282_,
            v___y_6283_,
        );
    leanh::lean_dec(v___y_6283_);
    leanh::lean_dec_ref(v___y_6282_);
    return v_res_6285_;
}
pub unsafe fn l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(
    mut v_declName_6286_: *mut leanh::LeanObject,
    mut v___y_6287_: *mut leanh::LeanObject,
    mut v___y_6288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6294_: u8 = 0;
    let mut v___x_6295_: u8 = 0;
    let mut v___x_6296_: u8 = 0;
    let mut v___x_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: u8 = 0;
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6290_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v_declName_6286_, v___y_6288_);
                v_a_6291_ = leanh::lean_ctor_get(v___x_6290_, 0);
                v_isSharedCheck_6306_ = (!leanh::lean_is_exclusive(v___x_6290_)) as u8;
                if v_isSharedCheck_6306_ == 0 {
                    v___x_6293_ = v___x_6290_;
                    v_isShared_6294_ = v_isSharedCheck_6306_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6291_);
                    leanh::lean_dec(v___x_6290_);
                    v___x_6293_ = leanh::lean_box(0);
                    v_isShared_6294_ = v_isSharedCheck_6306_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6295_ = (leanh::lean_unbox(v_a_6291_) as u8);
                leanh::lean_dec(v_a_6291_);
                if v___x_6295_ == 2 {
                    v___x_6296_ = 1;
                    v___x_6297_ = leanh::lean_box((v___x_6296_) as usize);
                    if v_isShared_6294_ == 0 {
                        leanh::lean_ctor_set(v___x_6293_, 0, v___x_6297_);
                        v___x_6299_ = v___x_6293_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6300_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6300_, 0, v___x_6297_);
                        v___x_6299_ = v_reuseFailAlloc_6300_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6301_ = 0;
                    v___x_6302_ = leanh::lean_box((v___x_6301_) as usize);
                    if v_isShared_6294_ == 0 {
                        leanh::lean_ctor_set(v___x_6293_, 0, v___x_6302_);
                        v___x_6304_ = v___x_6293_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6305_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6305_, 0, v___x_6302_);
                        v___x_6304_ = v_reuseFailAlloc_6305_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6299_;
            }
            3 => {
                return v___x_6304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0___boxed(
    mut v_declName_6307_: *mut leanh::LeanObject,
    mut v___y_6308_: *mut leanh::LeanObject,
    mut v___y_6309_: *mut leanh::LeanObject,
    mut v___y_6310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6311_ = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(
        v_declName_6307_,
        v___y_6308_,
        v___y_6309_,
    );
    leanh::lean_dec(v___y_6309_);
    leanh::lean_dec_ref(v___y_6308_);
    return v_res_6311_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(
    mut v_canUnfold_x3f_6312_: *mut leanh::LeanObject,
    mut v_cfg_6313_: *mut leanh::LeanObject,
    mut v_info_6314_: *mut leanh::LeanObject,
    mut v___y_6315_: *mut leanh::LeanObject,
    mut v___y_6316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: u8 = 0;
    let mut v_transparency_6322_: u8 = 0;
    let mut v___x_6323_: u8 = 0;
    let mut v___x_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6326_: u8 = 0;
    let mut v___x_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6331_: u8 = 0;
    let mut v_unused_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6337_: u8 = 0;
    let mut v___x_6338_: u8 = 0;
    let mut v___x_6339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6346_: u8 = 0;
    let mut v___x_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6349_: u8 = 0;
    let mut v___x_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6354_: u8 = 0;
    let mut v___y_6356_: u8 = 0;
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6365_: u8 = 0;
    let mut v___x_6366_: u8 = 0;
    let mut v___x_6367_: u8 = 0;
    let mut v___x_6368_: u8 = 0;
    let mut v___x_6369_: u8 = 0;
    let mut v___x_6370_: u8 = 0;
    let mut v___x_6371_: u8 = 0;
    let mut v___x_6372_: u8 = 0;
    let mut v___x_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6377_: u8 = 0;
    let mut v_isSharedCheck_6378_: u8 = 0;
    let mut v_unused_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6384_: u8 = 0;
    let mut v___x_6385_: u8 = 0;
    let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6390_: u8 = 0;
    let mut v_unused_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6318_ = l_Lean_ConstantInfo_name(v_info_6314_);
                v___x_6319_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v___x_6318_, v___y_6316_);
                if leanh::lean_obj_tag(v___x_6319_) == 0 {
                    v_a_6320_ = leanh::lean_ctor_get(v___x_6319_, 0);
                    leanh::lean_inc(v_a_6320_);
                    v___x_6321_ = (leanh::lean_unbox(v_a_6320_) as u8);
                    if v___x_6321_ == 0 {
                        if leanh::lean_obj_tag(v_canUnfold_x3f_6312_) == 0 {
                            leanh::lean_dec_ref(v_info_6314_);
                            v_transparency_6322_ =
                                leanh::lean_ctor_get_uint8(v_cfg_6313_, 9 as u32);
                            leanh::lean_dec_ref(v_cfg_6313_);
                            v___x_6323_ = 1;
                            match v_transparency_6322_ {
                                4 => {
                                    leanh::lean_dec(v_a_6320_);
                                    leanh::lean_dec(v___x_6318_);
                                    return v___x_6319_;
                                }
                                0 => {
                                    leanh::lean_dec(v_a_6320_);
                                    leanh::lean_dec(v___x_6318_);
                                    v_isSharedCheck_6331_ =
                                        (!leanh::lean_is_exclusive(v___x_6319_)) as u8;
                                    if v_isSharedCheck_6331_ == 0 {
                                        v_unused_6332_ =
                                            leanh::lean_ctor_get(v___x_6319_, 0);
                                        leanh::lean_dec(v_unused_6332_);
                                        v___x_6325_ = v___x_6319_;
                                        v_isShared_6326_ = v_isSharedCheck_6331_;
                                        state = 1;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_6319_);
                                        v___x_6325_ = leanh::lean_box(0);
                                        v_isShared_6326_ = v_isSharedCheck_6331_;
                                        state = 1;
                                        continue;
                                    }
                                }
                                1 => {
                                    leanh::lean_dec_ref_known(v___x_6319_, 1);
                                    v___x_6333_ = l_Lean_isIrreducible___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__0(v___x_6318_, v___y_6315_, v___y_6316_);
                                    if leanh::lean_obj_tag(v___x_6333_) == 0 {
                                        v_a_6334_ = leanh::lean_ctor_get(v___x_6333_, 0);
                                        v_isSharedCheck_6346_ =
                                            (!leanh::lean_is_exclusive(v___x_6333_)) as u8;
                                        if v_isSharedCheck_6346_ == 0 {
                                            v___x_6336_ = v___x_6333_;
                                            v_isShared_6337_ = v_isSharedCheck_6346_;
                                            state = 3;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_6334_);
                                            leanh::lean_dec(v___x_6333_);
                                            v___x_6336_ = leanh::lean_box(0);
                                            v_isShared_6337_ = v_isSharedCheck_6346_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_a_6320_);
                                        return v___x_6333_;
                                    }
                                }
                                _ => {
                                    leanh::lean_dec(v_a_6320_);
                                    v_isSharedCheck_6378_ =
                                        (!leanh::lean_is_exclusive(v___x_6319_)) as u8;
                                    if v_isSharedCheck_6378_ == 0 {
                                        v_unused_6379_ =
                                            leanh::lean_ctor_get(v___x_6319_, 0);
                                        leanh::lean_dec(v_unused_6379_);
                                        v___x_6348_ = v___x_6319_;
                                        v_isShared_6349_ = v_isSharedCheck_6378_;
                                        state = 6;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_6319_);
                                        v___x_6348_ = leanh::lean_box(0);
                                        v_isShared_6349_ = v_isSharedCheck_6378_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec_ref_known(v___x_6319_, 1);
                            leanh::lean_dec(v_a_6320_);
                            leanh::lean_dec(v___x_6318_);
                            v_val_6380_ = leanh::lean_ctor_get(v_canUnfold_x3f_6312_, 0);
                            leanh::lean_inc(v_val_6380_);
                            leanh::lean_dec_ref_known(v_canUnfold_x3f_6312_, 1);
                            leanh::lean_inc(v___y_6316_);
                            leanh::lean_inc_ref(v___y_6315_);
                            v___x_6381_ = leanh::lean_apply_5(
                                v_val_6380_,
                                v_cfg_6313_,
                                v_info_6314_,
                                v___y_6315_,
                                v___y_6316_,
                                leanh::lean_box(0),
                            );
                            return v___x_6381_;
                        }
                    } else {
                        leanh::lean_dec(v_a_6320_);
                        leanh::lean_dec(v___x_6318_);
                        leanh::lean_dec_ref(v_info_6314_);
                        leanh::lean_dec_ref(v_cfg_6313_);
                        leanh::lean_dec(v_canUnfold_x3f_6312_);
                        v_isSharedCheck_6390_ =
                            (!leanh::lean_is_exclusive(v___x_6319_)) as u8;
                        if v_isSharedCheck_6390_ == 0 {
                            v_unused_6391_ = leanh::lean_ctor_get(v___x_6319_, 0);
                            leanh::lean_dec(v_unused_6391_);
                            v___x_6383_ = v___x_6319_;
                            v_isShared_6384_ = v_isSharedCheck_6390_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6319_);
                            v___x_6383_ = leanh::lean_box(0);
                            v_isShared_6384_ = v_isSharedCheck_6390_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_6318_);
                    leanh::lean_dec_ref(v_info_6314_);
                    leanh::lean_dec_ref(v_cfg_6313_);
                    leanh::lean_dec(v_canUnfold_x3f_6312_);
                    return v___x_6319_;
                }
            }
            1 => {
                v___x_6327_ = leanh::lean_box((v___x_6323_) as usize);
                if v_isShared_6326_ == 0 {
                    leanh::lean_ctor_set(v___x_6325_, 0, v___x_6327_);
                    v___x_6329_ = v___x_6325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6330_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6330_, 0, v___x_6327_);
                    v___x_6329_ = v_reuseFailAlloc_6330_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6329_;
            }
            3 => {
                v___x_6338_ = (leanh::lean_unbox(v_a_6334_) as u8);
                leanh::lean_dec(v_a_6334_);
                if v___x_6338_ == 0 {
                    leanh::lean_dec(v_a_6320_);
                    v___x_6339_ = leanh::lean_box((v___x_6323_) as usize);
                    if v_isShared_6337_ == 0 {
                        leanh::lean_ctor_set(v___x_6336_, 0, v___x_6339_);
                        v___x_6341_ = v___x_6336_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6342_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6342_, 0, v___x_6339_);
                        v___x_6341_ = v_reuseFailAlloc_6342_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_6337_ == 0 {
                        leanh::lean_ctor_set(v___x_6336_, 0, v_a_6320_);
                        v___x_6344_ = v___x_6336_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6345_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6345_, 0, v_a_6320_);
                        v___x_6344_ = v_reuseFailAlloc_6345_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6341_;
            }
            5 => {
                return v___x_6344_;
            }
            6 => {
                v___x_6350_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard_spec__1___redArg(v___x_6318_, v___y_6316_);
                v_a_6351_ = leanh::lean_ctor_get(v___x_6350_, 0);
                v_isSharedCheck_6377_ = (!leanh::lean_is_exclusive(v___x_6350_)) as u8;
                if v_isSharedCheck_6377_ == 0 {
                    v___x_6353_ = v___x_6350_;
                    v_isShared_6354_ = v_isSharedCheck_6377_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6351_);
                    leanh::lean_dec(v___x_6350_);
                    v___x_6353_ = leanh::lean_box(0);
                    v_isShared_6354_ = v_isSharedCheck_6377_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6365_ = 0;
                v___x_6366_ = (leanh::lean_unbox(v_a_6351_) as u8);
                v___x_6367_ = l_Lean_instBEqReducibilityStatus_beq(v___x_6366_, v___x_6365_);
                if v___x_6367_ == 0 {
                    leanh::lean_del_object(v___x_6348_);
                    v___x_6368_ = 3;
                    v___x_6369_ =
                        l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_6322_, v___x_6368_);
                    if v___x_6369_ == 0 {
                        leanh::lean_dec(v_a_6351_);
                        v___y_6356_ = v___x_6369_;
                        state = 8;
                        continue;
                    } else {
                        v___x_6370_ = 3;
                        v___x_6371_ = (leanh::lean_unbox(v_a_6351_) as u8);
                        leanh::lean_dec(v_a_6351_);
                        v___x_6372_ =
                            l_Lean_instBEqReducibilityStatus_beq(v___x_6371_, v___x_6370_);
                        v___y_6356_ = v___x_6372_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6353_);
                    leanh::lean_dec(v_a_6351_);
                    v___x_6373_ = leanh::lean_box((v___x_6323_) as usize);
                    if v_isShared_6349_ == 0 {
                        leanh::lean_ctor_set(v___x_6348_, 0, v___x_6373_);
                        v___x_6375_ = v___x_6348_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_6376_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6376_, 0, v___x_6373_);
                        v___x_6375_ = v_reuseFailAlloc_6376_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v___y_6356_ == 0 {
                    v___x_6357_ = leanh::lean_box((v___y_6356_) as usize);
                    if v_isShared_6354_ == 0 {
                        leanh::lean_ctor_set(v___x_6353_, 0, v___x_6357_);
                        v___x_6359_ = v___x_6353_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6360_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6360_, 0, v___x_6357_);
                        v___x_6359_ = v_reuseFailAlloc_6360_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___x_6361_ = leanh::lean_box((v___x_6323_) as usize);
                    if v_isShared_6354_ == 0 {
                        leanh::lean_ctor_set(v___x_6353_, 0, v___x_6361_);
                        v___x_6363_ = v___x_6353_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_6364_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6364_, 0, v___x_6361_);
                        v___x_6363_ = v_reuseFailAlloc_6364_;
                        state = 10;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_6359_;
            }
            10 => {
                return v___x_6363_;
            }
            11 => {
                return v___x_6375_;
            }
            12 => {
                v___x_6385_ = 0;
                v___x_6386_ = leanh::lean_box((v___x_6385_) as usize);
                if v_isShared_6384_ == 0 {
                    leanh::lean_ctor_set(v___x_6383_, 0, v___x_6386_);
                    v___x_6388_ = v___x_6383_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6389_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6389_, 0, v___x_6386_);
                    v___x_6388_ = v_reuseFailAlloc_6389_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed(
    mut v_canUnfold_x3f_6392_: *mut leanh::LeanObject,
    mut v_cfg_6393_: *mut leanh::LeanObject,
    mut v_info_6394_: *mut leanh::LeanObject,
    mut v___y_6395_: *mut leanh::LeanObject,
    mut v___y_6396_: *mut leanh::LeanObject,
    mut v___y_6397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6398_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0(
        v_canUnfold_x3f_6392_,
        v_cfg_6393_,
        v_info_6394_,
        v___y_6395_,
        v___y_6396_,
    );
    leanh::lean_dec(v___y_6396_);
    leanh::lean_dec_ref(v___y_6395_);
    return v_res_6398_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(
    mut v_x_6399_: *mut leanh::LeanObject,
    mut v_a_6400_: *mut leanh::LeanObject,
    mut v_a_6401_: *mut leanh::LeanObject,
    mut v_a_6402_: *mut leanh::LeanObject,
    mut v_a_6403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_keyedConfig_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_6406_: u8 = 0;
    let mut v_zetaDeltaSet_6407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_6413_: u8 = 0;
    let mut v_inTypeClassResolution_6414_: u8 = 0;
    let mut v_cacheInferType_6415_: u8 = 0;
    let mut v___f_6416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_6405_ = leanh::lean_ctor_get(v_a_6400_, 0);
    v_trackZetaDelta_6406_ = leanh::lean_ctor_get_uint8(
        v_a_6400_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_6407_ = leanh::lean_ctor_get(v_a_6400_, 1);
    v_lctx_6408_ = leanh::lean_ctor_get(v_a_6400_, 2);
    v_localInstances_6409_ = leanh::lean_ctor_get(v_a_6400_, 3);
    v_defEqCtx_x3f_6410_ = leanh::lean_ctor_get(v_a_6400_, 4);
    v_synthPendingDepth_6411_ = leanh::lean_ctor_get(v_a_6400_, 5);
    v_canUnfold_x3f_6412_ = leanh::lean_ctor_get(v_a_6400_, 6);
    v_univApprox_6413_ = leanh::lean_ctor_get_uint8(
        v_a_6400_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_6414_ = leanh::lean_ctor_get_uint8(
        v_a_6400_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
    );
    v_cacheInferType_6415_ = leanh::lean_ctor_get_uint8(
        v_a_6400_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
    );
    leanh::lean_inc(v_canUnfold_x3f_6412_);
    v___f_6416_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_6416_, 0, v_canUnfold_x3f_6412_);
    v___x_6417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6417_, 0, v___f_6416_);
    leanh::lean_inc(v_synthPendingDepth_6411_);
    leanh::lean_inc(v_defEqCtx_x3f_6410_);
    leanh::lean_inc_ref(v_localInstances_6409_);
    leanh::lean_inc_ref(v_lctx_6408_);
    leanh::lean_inc(v_zetaDeltaSet_6407_);
    leanh::lean_inc_ref(v_keyedConfig_6405_);
    v___x_6418_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
    leanh::lean_ctor_set(v___x_6418_, 0, v_keyedConfig_6405_);
    leanh::lean_ctor_set(v___x_6418_, 1, v_zetaDeltaSet_6407_);
    leanh::lean_ctor_set(v___x_6418_, 2, v_lctx_6408_);
    leanh::lean_ctor_set(v___x_6418_, 3, v_localInstances_6409_);
    leanh::lean_ctor_set(v___x_6418_, 4, v_defEqCtx_x3f_6410_);
    leanh::lean_ctor_set(v___x_6418_, 5, v_synthPendingDepth_6411_);
    leanh::lean_ctor_set(v___x_6418_, 6, v___x_6417_);
    leanh::lean_ctor_set_uint8(
        v___x_6418_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_6406_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_6418_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_6413_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_6418_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_6414_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_6418_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
        v_cacheInferType_6415_,
    );
    leanh::lean_inc(v_a_6403_);
    leanh::lean_inc_ref(v_a_6402_);
    leanh::lean_inc(v_a_6401_);
    v___x_6419_ = leanh::lean_apply_5(
        v_x_6399_,
        v___x_6418_,
        v_a_6401_,
        v_a_6402_,
        v_a_6403_,
        leanh::lean_box(0),
    );
    return v___x_6419_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg___boxed(
    mut v_x_6420_: *mut leanh::LeanObject,
    mut v_a_6421_: *mut leanh::LeanObject,
    mut v_a_6422_: *mut leanh::LeanObject,
    mut v_a_6423_: *mut leanh::LeanObject,
    mut v_a_6424_: *mut leanh::LeanObject,
    mut v_a_6425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6426_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(
        v_x_6420_, v_a_6421_, v_a_6422_, v_a_6423_, v_a_6424_,
    );
    leanh::lean_dec(v_a_6424_);
    leanh::lean_dec_ref(v_a_6423_);
    leanh::lean_dec(v_a_6422_);
    leanh::lean_dec_ref(v_a_6421_);
    return v_res_6426_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(
    mut v_00_u03b1_6427_: *mut leanh::LeanObject,
    mut v_x_6428_: *mut leanh::LeanObject,
    mut v_a_6429_: *mut leanh::LeanObject,
    mut v_a_6430_: *mut leanh::LeanObject,
    mut v_a_6431_: *mut leanh::LeanObject,
    mut v_a_6432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6434_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(
        v_x_6428_, v_a_6429_, v_a_6430_, v_a_6431_, v_a_6432_,
    );
    return v___x_6434_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___boxed(
    mut v_00_u03b1_6435_: *mut leanh::LeanObject,
    mut v_x_6436_: *mut leanh::LeanObject,
    mut v_a_6437_: *mut leanh::LeanObject,
    mut v_a_6438_: *mut leanh::LeanObject,
    mut v_a_6439_: *mut leanh::LeanObject,
    mut v_a_6440_: *mut leanh::LeanObject,
    mut v_a_6441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6442_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard(
        v_00_u03b1_6435_,
        v_x_6436_,
        v_a_6437_,
        v_a_6438_,
        v_a_6439_,
        v_a_6440_,
    );
    leanh::lean_dec(v_a_6440_);
    leanh::lean_dec_ref(v_a_6439_);
    leanh::lean_dec(v_a_6438_);
    leanh::lean_dec_ref(v_a_6437_);
    return v_res_6442_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(
    mut v_a_6443_: *mut leanh::LeanObject,
    mut v_a_6444_: *mut leanh::LeanObject,
    mut v_a_6445_: *mut leanh::LeanObject,
    mut v_a_6446_: *mut leanh::LeanObject,
    mut v_a_6447_: *mut leanh::LeanObject,
    mut v_a_6448_: *mut leanh::LeanObject,
    mut v_a_6449_: *mut leanh::LeanObject,
    mut v_a_6450_: *mut leanh::LeanObject,
    mut v_a_6451_: *mut leanh::LeanObject,
    mut v_a_6452_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6454_ = l_Lean_Meta_Sym_Simp_simpCond(
        v_a_6443_, v_a_6444_, v_a_6445_, v_a_6446_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_,
        v_a_6451_, v_a_6452_,
    );
    return v___x_6454_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___boxed(
    mut v_a_6455_: *mut leanh::LeanObject,
    mut v_a_6456_: *mut leanh::LeanObject,
    mut v_a_6457_: *mut leanh::LeanObject,
    mut v_a_6458_: *mut leanh::LeanObject,
    mut v_a_6459_: *mut leanh::LeanObject,
    mut v_a_6460_: *mut leanh::LeanObject,
    mut v_a_6461_: *mut leanh::LeanObject,
    mut v_a_6462_: *mut leanh::LeanObject,
    mut v_a_6463_: *mut leanh::LeanObject,
    mut v_a_6464_: *mut leanh::LeanObject,
    mut v_a_6465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6466_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond(
        v_a_6455_, v_a_6456_, v_a_6457_, v_a_6458_, v_a_6459_, v_a_6460_, v_a_6461_, v_a_6462_,
        v_a_6463_, v_a_6464_,
    );
    leanh::lean_dec(v_a_6464_);
    leanh::lean_dec_ref(v_a_6463_);
    leanh::lean_dec(v_a_6462_);
    leanh::lean_dec_ref(v_a_6461_);
    leanh::lean_dec(v_a_6460_);
    leanh::lean_dec_ref(v_a_6459_);
    leanh::lean_dec(v_a_6458_);
    leanh::lean_dec_ref(v_a_6457_);
    leanh::lean_dec(v_a_6456_);
    return v_res_6466_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_()
-> *mut leanh::LeanObject {
    let mut v___f_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6493_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_;
    v___x_6494_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_;
    v___x_6495_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__8_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_;
    v___x_6496_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_6494_, v___x_6495_, v___f_6493_);
    return v___x_6496_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15____boxed(
    mut v_a_6497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6498_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_();
    return v_res_6498_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___f_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: u8 = 0;
    let mut v___x_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6500_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__0_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_;
    v___x_6501_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69___closed__4_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_;
    v___x_6502_ = 0;
    v___x_6503_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_6501_, v___x_6502_, v___f_6500_);
    return v___x_6503_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17____boxed(
    mut v_a_6504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6505_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_();
    return v_res_6505_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(
    mut v_msgData_6506_: *mut leanh::LeanObject,
    mut v___y_6507_: *mut leanh::LeanObject,
    mut v___y_6508_: *mut leanh::LeanObject,
    mut v___y_6509_: *mut leanh::LeanObject,
    mut v___y_6510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6512_ = lean_st_ref_get(v___y_6510_);
    v_env_6513_ = leanh::lean_ctor_get(v___x_6512_, 0);
    leanh::lean_inc_ref(v_env_6513_);
    leanh::lean_dec(v___x_6512_);
    v___x_6514_ = lean_st_ref_get(v___y_6508_);
    v_mctx_6515_ = leanh::lean_ctor_get(v___x_6514_, 0);
    leanh::lean_inc_ref(v_mctx_6515_);
    leanh::lean_dec(v___x_6514_);
    v_lctx_6516_ = leanh::lean_ctor_get(v___y_6507_, 2);
    v_options_6517_ = leanh::lean_ctor_get(v___y_6509_, 2);
    leanh::lean_inc_ref(v_options_6517_);
    leanh::lean_inc_ref(v_lctx_6516_);
    v___x_6518_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6518_, 0, v_env_6513_);
    leanh::lean_ctor_set(v___x_6518_, 1, v_mctx_6515_);
    leanh::lean_ctor_set(v___x_6518_, 2, v_lctx_6516_);
    leanh::lean_ctor_set(v___x_6518_, 3, v_options_6517_);
    v___x_6519_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6519_, 0, v___x_6518_);
    leanh::lean_ctor_set(v___x_6519_, 1, v_msgData_6506_);
    v___x_6520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6520_, 0, v___x_6519_);
    return v___x_6520_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0___boxed(
    mut v_msgData_6521_: *mut leanh::LeanObject,
    mut v___y_6522_: *mut leanh::LeanObject,
    mut v___y_6523_: *mut leanh::LeanObject,
    mut v___y_6524_: *mut leanh::LeanObject,
    mut v___y_6525_: *mut leanh::LeanObject,
    mut v___y_6526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6527_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msgData_6521_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_);
    leanh::lean_dec(v___y_6525_);
    leanh::lean_dec_ref(v___y_6524_);
    leanh::lean_dec(v___y_6523_);
    leanh::lean_dec_ref(v___y_6522_);
    return v_res_6527_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_6528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: f64 = 0.0;
    v___x_6528_ = leanh::lean_unsigned_to_nat(0);
    v___x_6529_ = lean_float_of_nat(v___x_6528_);
    return v___x_6529_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(
    mut v_cls_6533_: *mut leanh::LeanObject,
    mut v_msg_6534_: *mut leanh::LeanObject,
    mut v___y_6535_: *mut leanh::LeanObject,
    mut v___y_6536_: *mut leanh::LeanObject,
    mut v___y_6537_: *mut leanh::LeanObject,
    mut v___y_6538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6545_: u8 = 0;
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6558_: u8 = 0;
    let mut v_tid_6559_: u64 = 0;
    let mut v_traces_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6563_: u8 = 0;
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: f64 = 0.0;
    let mut v___x_6566_: u8 = 0;
    let mut v___x_6567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6584_: u8 = 0;
    let mut v_isSharedCheck_6585_: u8 = 0;
    let mut v_isSharedCheck_6586_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6540_ = leanh::lean_ctor_get(v___y_6537_, 5);
                v___x_6541_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0_spec__0(v_msg_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_);
                v_a_6542_ = leanh::lean_ctor_get(v___x_6541_, 0);
                v_isSharedCheck_6586_ = (!leanh::lean_is_exclusive(v___x_6541_)) as u8;
                if v_isSharedCheck_6586_ == 0 {
                    v___x_6544_ = v___x_6541_;
                    v_isShared_6545_ = v_isSharedCheck_6586_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6542_);
                    leanh::lean_dec(v___x_6541_);
                    v___x_6544_ = leanh::lean_box(0);
                    v_isShared_6545_ = v_isSharedCheck_6586_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6546_ = lean_st_ref_take(v___y_6538_);
                v_traceState_6547_ = leanh::lean_ctor_get(v___x_6546_, 4);
                v_env_6548_ = leanh::lean_ctor_get(v___x_6546_, 0);
                v_nextMacroScope_6549_ = leanh::lean_ctor_get(v___x_6546_, 1);
                v_ngen_6550_ = leanh::lean_ctor_get(v___x_6546_, 2);
                v_auxDeclNGen_6551_ = leanh::lean_ctor_get(v___x_6546_, 3);
                v_cache_6552_ = leanh::lean_ctor_get(v___x_6546_, 5);
                v_messages_6553_ = leanh::lean_ctor_get(v___x_6546_, 6);
                v_infoState_6554_ = leanh::lean_ctor_get(v___x_6546_, 7);
                v_snapshotTasks_6555_ = leanh::lean_ctor_get(v___x_6546_, 8);
                v_isSharedCheck_6585_ = (!leanh::lean_is_exclusive(v___x_6546_)) as u8;
                if v_isSharedCheck_6585_ == 0 {
                    v___x_6557_ = v___x_6546_;
                    v_isShared_6558_ = v_isSharedCheck_6585_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6555_);
                    leanh::lean_inc(v_infoState_6554_);
                    leanh::lean_inc(v_messages_6553_);
                    leanh::lean_inc(v_cache_6552_);
                    leanh::lean_inc(v_traceState_6547_);
                    leanh::lean_inc(v_auxDeclNGen_6551_);
                    leanh::lean_inc(v_ngen_6550_);
                    leanh::lean_inc(v_nextMacroScope_6549_);
                    leanh::lean_inc(v_env_6548_);
                    leanh::lean_dec(v___x_6546_);
                    v___x_6557_ = leanh::lean_box(0);
                    v_isShared_6558_ = v_isSharedCheck_6585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6559_ = leanh::lean_ctor_get_uint64(
                    v_traceState_6547_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6560_ = leanh::lean_ctor_get(v_traceState_6547_, 0);
                v_isSharedCheck_6584_ =
                    (!leanh::lean_is_exclusive(v_traceState_6547_)) as u8;
                if v_isSharedCheck_6584_ == 0 {
                    v___x_6562_ = v_traceState_6547_;
                    v_isShared_6563_ = v_isSharedCheck_6584_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_6560_);
                    leanh::lean_dec(v_traceState_6547_);
                    v___x_6562_ = leanh::lean_box(0);
                    v_isShared_6563_ = v_isSharedCheck_6584_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6564_ = leanh::lean_box(0);
                v___x_6565_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__0);
                v___x_6566_ = 0;
                v___x_6567_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__1;
                v___x_6568_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_6568_, 0, v_cls_6533_);
                leanh::lean_ctor_set(v___x_6568_, 1, v___x_6564_);
                leanh::lean_ctor_set(v___x_6568_, 2, v___x_6567_);
                leanh::lean_ctor_set_float(
                    v___x_6568_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_6565_,
                );
                leanh::lean_ctor_set_float(
                    v___x_6568_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6565_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6568_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6566_,
                );
                v___x_6569_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___closed__2;
                v___x_6570_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6570_, 0, v___x_6568_);
                leanh::lean_ctor_set(v___x_6570_, 1, v_a_6542_);
                leanh::lean_ctor_set(v___x_6570_, 2, v___x_6569_);
                leanh::lean_inc(v_ref_6540_);
                v___x_6571_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6571_, 0, v_ref_6540_);
                leanh::lean_ctor_set(v___x_6571_, 1, v___x_6570_);
                v___x_6572_ = l_Lean_PersistentArray_push___redArg(v_traces_6560_, v___x_6571_);
                if v_isShared_6563_ == 0 {
                    leanh::lean_ctor_set(v___x_6562_, 0, v___x_6572_);
                    v___x_6574_ = v___x_6562_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6583_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6583_, 0, v___x_6572_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6583_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_6559_,
                    );
                    v___x_6574_ = v_reuseFailAlloc_6583_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6558_ == 0 {
                    leanh::lean_ctor_set(v___x_6557_, 4, v___x_6574_);
                    v___x_6576_ = v___x_6557_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6582_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 0, v_env_6548_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 1, v_nextMacroScope_6549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 2, v_ngen_6550_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 3, v_auxDeclNGen_6551_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 4, v___x_6574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 5, v_cache_6552_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 6, v_messages_6553_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 7, v_infoState_6554_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6582_, 8, v_snapshotTasks_6555_);
                    v___x_6576_ = v_reuseFailAlloc_6582_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6577_ = lean_st_ref_set(v___y_6538_, v___x_6576_);
                v___x_6578_ = leanh::lean_box(0);
                if v_isShared_6545_ == 0 {
                    leanh::lean_ctor_set(v___x_6544_, 0, v___x_6578_);
                    v___x_6580_ = v___x_6544_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6581_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6581_, 0, v___x_6578_);
                    v___x_6580_ = v_reuseFailAlloc_6581_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg___boxed(
    mut v_cls_6587_: *mut leanh::LeanObject,
    mut v_msg_6588_: *mut leanh::LeanObject,
    mut v___y_6589_: *mut leanh::LeanObject,
    mut v___y_6590_: *mut leanh::LeanObject,
    mut v___y_6591_: *mut leanh::LeanObject,
    mut v___y_6592_: *mut leanh::LeanObject,
    mut v___y_6593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6594_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(
        v_cls_6587_,
        v_msg_6588_,
        v___y_6589_,
        v___y_6590_,
        v___y_6591_,
        v___y_6592_,
    );
    leanh::lean_dec(v___y_6592_);
    leanh::lean_dec_ref(v___y_6591_);
    leanh::lean_dec(v___y_6590_);
    leanh::lean_dec_ref(v___y_6589_);
    return v_res_6594_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6605_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2;
    v___x_6606_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4;
    v___x_6607_ = l_Lean_Name_append(v___x_6606_, v___x_6605_);
    return v___x_6607_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6609_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__6;
    v___x_6610_ = l_Lean_stringToMessageData(v___x_6609_);
    return v___x_6610_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6612_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__8;
    v___x_6613_ = l_Lean_stringToMessageData(v___x_6612_);
    return v___x_6613_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(
    mut v_e_6616_: *mut leanh::LeanObject,
    mut v_a_6617_: *mut leanh::LeanObject,
    mut v_a_6618_: *mut leanh::LeanObject,
    mut v_a_6619_: *mut leanh::LeanObject,
    mut v_a_6620_: *mut leanh::LeanObject,
    mut v_a_6621_: *mut leanh::LeanObject,
    mut v_a_6622_: *mut leanh::LeanObject,
    mut v_a_6623_: *mut leanh::LeanObject,
    mut v_a_6624_: *mut leanh::LeanObject,
    mut v_a_6625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6632_: u8 = 0;
    let mut v_val_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6644_: u8 = 0;
    let mut v___x_6645_: u8 = 0;
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6650_: u8 = 0;
    let mut v_a_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6654_: u8 = 0;
    let mut v___x_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6658_: u8 = 0;
    let mut v_options_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6660_: u8 = 0;
    let mut v_inheritedTraceOptions_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: u8 = 0;
    let mut v___x_6665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6676_: u8 = 0;
    let mut v___x_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6680_: u8 = 0;
    let mut v___x_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6685_: u8 = 0;
    let mut v_a_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6689_: u8 = 0;
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6693_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_6616_);
                v___x_6627_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_reduceRecMatcher_x3f___boxed as *mut core::ffi::c_void,
                    6,
                    1,
                );
                leanh::lean_closure_set(v___x_6627_, 0, v_e_6616_);
                v___x_6628_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(
                    v___x_6627_,
                    v_a_6622_,
                    v_a_6623_,
                    v_a_6624_,
                    v_a_6625_,
                );
                if leanh::lean_obj_tag(v___x_6628_) == 0 {
                    v_a_6629_ = leanh::lean_ctor_get(v___x_6628_, 0);
                    v_isSharedCheck_6685_ = (!leanh::lean_is_exclusive(v___x_6628_)) as u8;
                    if v_isSharedCheck_6685_ == 0 {
                        v___x_6631_ = v___x_6628_;
                        v_isShared_6632_ = v_isSharedCheck_6685_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6629_);
                        leanh::lean_dec(v___x_6628_);
                        v___x_6631_ = leanh::lean_box(0);
                        v_isShared_6632_ = v_isSharedCheck_6685_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6616_);
                    v_a_6686_ = leanh::lean_ctor_get(v___x_6628_, 0);
                    v_isSharedCheck_6693_ = (!leanh::lean_is_exclusive(v___x_6628_)) as u8;
                    if v_isSharedCheck_6693_ == 0 {
                        v___x_6688_ = v___x_6628_;
                        v_isShared_6689_ = v_isSharedCheck_6693_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6686_);
                        leanh::lean_dec(v___x_6628_);
                        v___x_6688_ = leanh::lean_box(0);
                        v_isShared_6689_ = v_isSharedCheck_6693_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6629_) == 1 {
                    leanh::lean_del_object(v___x_6631_);
                    v_val_6633_ = leanh::lean_ctor_get(v_a_6629_, 0);
                    leanh::lean_inc(v_val_6633_);
                    leanh::lean_dec_ref_known(v_a_6629_, 1);
                    v_options_6659_ = leanh::lean_ctor_get(v_a_6624_, 2);
                    v_hasTrace_6660_ = leanh::lean_ctor_get_uint8(
                        v_options_6659_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6660_ == 0 {
                        leanh::lean_dec_ref(v_e_6616_);
                        v___y_6635_ = v_a_6621_;
                        v___y_6636_ = v_a_6622_;
                        v___y_6637_ = v_a_6623_;
                        v___y_6638_ = v_a_6624_;
                        v___y_6639_ = v_a_6625_;
                        state = 2;
                        continue;
                    } else {
                        v_inheritedTraceOptions_6661_ = leanh::lean_ctor_get(v_a_6624_, 13);
                        v___x_6662_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__2;
                        v___x_6663_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__5,
                        );
                        v___x_6664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_6661_,
                            v_options_6659_,
                            v___x_6663_,
                        );
                        if v___x_6664_ == 0 {
                            leanh::lean_dec_ref(v_e_6616_);
                            v___y_6635_ = v_a_6621_;
                            v___y_6636_ = v_a_6622_;
                            v___y_6637_ = v_a_6623_;
                            v___y_6638_ = v_a_6624_;
                            v___y_6639_ = v_a_6625_;
                            state = 2;
                            continue;
                        } else {
                            v___x_6665_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7_once
                                ),
                                _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__7,
                            );
                            v___x_6666_ = l_Lean_indentExpr(v_e_6616_);
                            v___x_6667_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6667_, 0, v___x_6665_);
                            leanh::lean_ctor_set(v___x_6667_, 1, v___x_6666_);
                            v___x_6668_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once
                                ),
                                _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9,
                            );
                            v___x_6669_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6669_, 0, v___x_6667_);
                            leanh::lean_ctor_set(v___x_6669_, 1, v___x_6668_);
                            leanh::lean_inc(v_val_6633_);
                            v___x_6670_ = l_Lean_indentExpr(v_val_6633_);
                            v___x_6671_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_6671_, 0, v___x_6669_);
                            leanh::lean_ctor_set(v___x_6671_, 1, v___x_6670_);
                            v___x_6672_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_6662_, v___x_6671_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_);
                            if leanh::lean_obj_tag(v___x_6672_) == 0 {
                                leanh::lean_dec_ref_known(v___x_6672_, 1);
                                v___y_6635_ = v_a_6621_;
                                v___y_6636_ = v_a_6622_;
                                v___y_6637_ = v_a_6623_;
                                v___y_6638_ = v_a_6624_;
                                v___y_6639_ = v_a_6625_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec(v_val_6633_);
                                v_a_6673_ = leanh::lean_ctor_get(v___x_6672_, 0);
                                v_isSharedCheck_6680_ =
                                    (!leanh::lean_is_exclusive(v___x_6672_)) as u8;
                                if v_isSharedCheck_6680_ == 0 {
                                    v___x_6675_ = v___x_6672_;
                                    v_isShared_6676_ = v_isSharedCheck_6680_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6673_);
                                    leanh::lean_dec(v___x_6672_);
                                    v___x_6675_ = leanh::lean_box(0);
                                    v_isShared_6676_ = v_isSharedCheck_6680_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_6629_);
                    leanh::lean_dec_ref(v_e_6616_);
                    v___x_6681_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10;
                    if v_isShared_6632_ == 0 {
                        leanh::lean_ctor_set(v___x_6631_, 0, v___x_6681_);
                        v___x_6683_ = v___x_6631_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6684_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6684_, 0, v___x_6681_);
                        v___x_6683_ = v_reuseFailAlloc_6684_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_6633_);
                v___x_6640_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
                    v_val_6633_,
                    v___y_6635_,
                    v___y_6636_,
                    v___y_6637_,
                    v___y_6638_,
                    v___y_6639_,
                );
                if leanh::lean_obj_tag(v___x_6640_) == 0 {
                    v_a_6641_ = leanh::lean_ctor_get(v___x_6640_, 0);
                    v_isSharedCheck_6650_ = (!leanh::lean_is_exclusive(v___x_6640_)) as u8;
                    if v_isSharedCheck_6650_ == 0 {
                        v___x_6643_ = v___x_6640_;
                        v_isShared_6644_ = v_isSharedCheck_6650_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6641_);
                        leanh::lean_dec(v___x_6640_);
                        v___x_6643_ = leanh::lean_box(0);
                        v_isShared_6644_ = v_isSharedCheck_6650_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_val_6633_);
                    v_a_6651_ = leanh::lean_ctor_get(v___x_6640_, 0);
                    v_isSharedCheck_6658_ = (!leanh::lean_is_exclusive(v___x_6640_)) as u8;
                    if v_isSharedCheck_6658_ == 0 {
                        v___x_6653_ = v___x_6640_;
                        v_isShared_6654_ = v_isSharedCheck_6658_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6651_);
                        leanh::lean_dec(v___x_6640_);
                        v___x_6653_ = leanh::lean_box(0);
                        v_isShared_6654_ = v_isSharedCheck_6658_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6645_ = 0;
                v___x_6646_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                leanh::lean_ctor_set(v___x_6646_, 0, v_val_6633_);
                leanh::lean_ctor_set(v___x_6646_, 1, v_a_6641_);
                leanh::lean_ctor_set_uint8(
                    v___x_6646_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_6645_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6646_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___x_6645_,
                );
                if v_isShared_6644_ == 0 {
                    leanh::lean_ctor_set(v___x_6643_, 0, v___x_6646_);
                    v___x_6648_ = v___x_6643_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6649_, 0, v___x_6646_);
                    v___x_6648_ = v_reuseFailAlloc_6649_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6648_;
            }
            5 => {
                if v_isShared_6654_ == 0 {
                    v___x_6656_ = v___x_6653_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6657_, 0, v_a_6651_);
                    v___x_6656_ = v_reuseFailAlloc_6657_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6656_;
            }
            7 => {
                if v_isShared_6676_ == 0 {
                    v___x_6678_ = v___x_6675_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6679_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6679_, 0, v_a_6673_);
                    v___x_6678_ = v_reuseFailAlloc_6679_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6678_;
            }
            9 => {
                return v___x_6683_;
            }
            10 => {
                if v_isShared_6689_ == 0 {
                    v___x_6691_ = v___x_6688_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6692_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6692_, 0, v_a_6686_);
                    v___x_6691_ = v_reuseFailAlloc_6692_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6691_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___boxed(
    mut v_e_6694_: *mut leanh::LeanObject,
    mut v_a_6695_: *mut leanh::LeanObject,
    mut v_a_6696_: *mut leanh::LeanObject,
    mut v_a_6697_: *mut leanh::LeanObject,
    mut v_a_6698_: *mut leanh::LeanObject,
    mut v_a_6699_: *mut leanh::LeanObject,
    mut v_a_6700_: *mut leanh::LeanObject,
    mut v_a_6701_: *mut leanh::LeanObject,
    mut v_a_6702_: *mut leanh::LeanObject,
    mut v_a_6703_: *mut leanh::LeanObject,
    mut v_a_6704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6705_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(
        v_e_6694_, v_a_6695_, v_a_6696_, v_a_6697_, v_a_6698_, v_a_6699_, v_a_6700_, v_a_6701_,
        v_a_6702_, v_a_6703_,
    );
    leanh::lean_dec(v_a_6703_);
    leanh::lean_dec_ref(v_a_6702_);
    leanh::lean_dec(v_a_6701_);
    leanh::lean_dec_ref(v_a_6700_);
    leanh::lean_dec(v_a_6699_);
    leanh::lean_dec_ref(v_a_6698_);
    leanh::lean_dec(v_a_6697_);
    leanh::lean_dec_ref(v_a_6696_);
    leanh::lean_dec(v_a_6695_);
    return v_res_6705_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(
    mut v_cls_6706_: *mut leanh::LeanObject,
    mut v_msg_6707_: *mut leanh::LeanObject,
    mut v___y_6708_: *mut leanh::LeanObject,
    mut v___y_6709_: *mut leanh::LeanObject,
    mut v___y_6710_: *mut leanh::LeanObject,
    mut v___y_6711_: *mut leanh::LeanObject,
    mut v___y_6712_: *mut leanh::LeanObject,
    mut v___y_6713_: *mut leanh::LeanObject,
    mut v___y_6714_: *mut leanh::LeanObject,
    mut v___y_6715_: *mut leanh::LeanObject,
    mut v___y_6716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6718_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(
        v_cls_6706_,
        v_msg_6707_,
        v___y_6713_,
        v___y_6714_,
        v___y_6715_,
        v___y_6716_,
    );
    return v___x_6718_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___boxed(
    mut v_cls_6719_: *mut leanh::LeanObject,
    mut v_msg_6720_: *mut leanh::LeanObject,
    mut v___y_6721_: *mut leanh::LeanObject,
    mut v___y_6722_: *mut leanh::LeanObject,
    mut v___y_6723_: *mut leanh::LeanObject,
    mut v___y_6724_: *mut leanh::LeanObject,
    mut v___y_6725_: *mut leanh::LeanObject,
    mut v___y_6726_: *mut leanh::LeanObject,
    mut v___y_6727_: *mut leanh::LeanObject,
    mut v___y_6728_: *mut leanh::LeanObject,
    mut v___y_6729_: *mut leanh::LeanObject,
    mut v___y_6730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6731_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0(
        v_cls_6719_,
        v_msg_6720_,
        v___y_6721_,
        v___y_6722_,
        v___y_6723_,
        v___y_6724_,
        v___y_6725_,
        v___y_6726_,
        v___y_6727_,
        v___y_6728_,
        v___y_6729_,
    );
    leanh::lean_dec(v___y_6729_);
    leanh::lean_dec_ref(v___y_6728_);
    leanh::lean_dec(v___y_6727_);
    leanh::lean_dec_ref(v___y_6726_);
    leanh::lean_dec(v___y_6725_);
    leanh::lean_dec_ref(v___y_6724_);
    leanh::lean_dec(v___y_6723_);
    leanh::lean_dec_ref(v___y_6722_);
    leanh::lean_dec(v___y_6721_);
    return v_res_6731_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(
    mut v_x_6746_: *mut leanh::LeanObject,
    mut v_a_6747_: *mut leanh::LeanObject,
    mut v_a_6748_: *mut leanh::LeanObject,
    mut v_a_6749_: *mut leanh::LeanObject,
    mut v_a_6750_: *mut leanh::LeanObject,
    mut v_a_6751_: *mut leanh::LeanObject,
    mut v_a_6752_: *mut leanh::LeanObject,
    mut v_a_6753_: *mut leanh::LeanObject,
    mut v_a_6754_: *mut leanh::LeanObject,
    mut v_a_6755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6757_: u8 = 0;
    let mut v___x_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_6761_: u8 = 0;
    let mut v___x_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6764_: u8 = 0;
    let mut v_contextDependent_6765_: u8 = 0;
    let mut v___x_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6769_: u8 = 0;
    let mut v___x_6770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6774_: u8 = 0;
    let mut v_unused_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_6776_: u8 = 0;
    let mut v_e_x27_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_6779_: u8 = 0;
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6782_: u8 = 0;
    let mut v___x_6783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6787_: u8 = 0;
    let mut v___y_6789_: u8 = 0;
    let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6800_: u8 = 0;
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6805_: u8 = 0;
    let mut v___y_6807_: u8 = 0;
    let mut v___x_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6814_: u8 = 0;
    let mut v_a_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6818_: u8 = 0;
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6822_: u8 = 0;
    let mut v_isSharedCheck_6823_: u8 = 0;
    let mut v_isSharedCheck_6824_: u8 = 0;
    let mut v_isSharedCheck_6825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6757_ = 0;
                v___x_6758_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___closed__0;
                leanh::lean_inc_ref(v_x_6746_);
                v___x_6759_ = l_Lean_Meta_Sym_Simp_simpInterlaced(
                    v_x_6746_,
                    v___x_6758_,
                    v_a_6747_,
                    v_a_6748_,
                    v_a_6749_,
                    v_a_6750_,
                    v_a_6751_,
                    v_a_6752_,
                    v_a_6753_,
                    v_a_6754_,
                    v_a_6755_,
                );
                if leanh::lean_obj_tag(v___x_6759_) == 0 {
                    v_a_6760_ = leanh::lean_ctor_get(v___x_6759_, 0);
                    leanh::lean_inc(v_a_6760_);
                    if leanh::lean_obj_tag(v_a_6760_) == 0 {
                        v_done_6761_ = leanh::lean_ctor_get_uint8(v_a_6760_, 0 as u32);
                        if v_done_6761_ == 0 {
                            v_isSharedCheck_6774_ =
                                (!leanh::lean_is_exclusive(v___x_6759_)) as u8;
                            if v_isSharedCheck_6774_ == 0 {
                                v_unused_6775_ = leanh::lean_ctor_get(v___x_6759_, 0);
                                leanh::lean_dec(v_unused_6775_);
                                v___x_6763_ = v___x_6759_;
                                v_isShared_6764_ = v_isSharedCheck_6774_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_6759_);
                                v___x_6763_ = leanh::lean_box(0);
                                v_isShared_6764_ = v_isSharedCheck_6774_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_a_6760_, 0);
                            leanh::lean_dec_ref(v_x_6746_);
                            return v___x_6759_;
                        }
                    } else {
                        v_done_6776_ = leanh::lean_ctor_get_uint8(
                            v_a_6760_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        if v_done_6776_ == 0 {
                            leanh::lean_dec_ref_known(v___x_6759_, 1);
                            v_e_x27_6777_ = leanh::lean_ctor_get(v_a_6760_, 0);
                            v_proof_6778_ = leanh::lean_ctor_get(v_a_6760_, 1);
                            v_contextDependent_6779_ = leanh::lean_ctor_get_uint8(
                                v_a_6760_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                    as u32,
                            );
                            v_isSharedCheck_6825_ =
                                (!leanh::lean_is_exclusive(v_a_6760_)) as u8;
                            if v_isSharedCheck_6825_ == 0 {
                                v___x_6781_ = v_a_6760_;
                                v_isShared_6782_ = v_isSharedCheck_6825_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_proof_6778_);
                                leanh::lean_inc(v_e_x27_6777_);
                                leanh::lean_dec(v_a_6760_);
                                v___x_6781_ = leanh::lean_box(0);
                                v_isShared_6782_ = v_isSharedCheck_6825_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_a_6760_, 2);
                            leanh::lean_dec_ref(v_x_6746_);
                            return v___x_6759_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_6746_);
                    return v___x_6759_;
                }
            }
            1 => {
                v_contextDependent_6765_ = leanh::lean_ctor_get_uint8(v_a_6760_, 1 as u32);
                leanh::lean_dec_ref_known(v_a_6760_, 0);
                v___x_6766_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(
                    v_x_6746_, v_a_6747_, v_a_6748_, v_a_6749_, v_a_6750_, v_a_6751_, v_a_6752_,
                    v_a_6753_, v_a_6754_, v_a_6755_,
                );
                if leanh::lean_obj_tag(v___x_6766_) == 0 {
                    v_a_6767_ = leanh::lean_ctor_get(v___x_6766_, 0);
                    leanh::lean_inc(v_a_6767_);
                    if v_contextDependent_6765_ == 0 {
                        leanh::lean_dec(v_a_6767_);
                        leanh::lean_del_object(v___x_6763_);
                        return v___x_6766_;
                    } else {
                        leanh::lean_dec_ref_known(v___x_6766_, 1);
                        v___y_6769_ = v___x_6757_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6763_);
                    return v___x_6766_;
                }
            }
            2 => {
                v___x_6770_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_6767_);
                if v_isShared_6764_ == 0 {
                    leanh::lean_ctor_set(v___x_6763_, 0, v___x_6770_);
                    v___x_6772_ = v___x_6763_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6773_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6773_, 0, v___x_6770_);
                    v___x_6772_ = v_reuseFailAlloc_6773_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6772_;
            }
            4 => {
                leanh::lean_inc_ref(v_e_x27_6777_);
                v___x_6783_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(
                    v_e_x27_6777_,
                    v_a_6747_,
                    v_a_6748_,
                    v_a_6749_,
                    v_a_6750_,
                    v_a_6751_,
                    v_a_6752_,
                    v_a_6753_,
                    v_a_6754_,
                    v_a_6755_,
                );
                if leanh::lean_obj_tag(v___x_6783_) == 0 {
                    v_a_6784_ = leanh::lean_ctor_get(v___x_6783_, 0);
                    v_isSharedCheck_6824_ = (!leanh::lean_is_exclusive(v___x_6783_)) as u8;
                    if v_isSharedCheck_6824_ == 0 {
                        v___x_6786_ = v___x_6783_;
                        v_isShared_6787_ = v_isSharedCheck_6824_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6784_);
                        leanh::lean_dec(v___x_6783_);
                        v___x_6786_ = leanh::lean_box(0);
                        v_isShared_6787_ = v_isSharedCheck_6824_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6781_);
                    leanh::lean_dec_ref(v_proof_6778_);
                    leanh::lean_dec_ref(v_e_x27_6777_);
                    leanh::lean_dec_ref(v_x_6746_);
                    return v___x_6783_;
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_6784_) == 0 {
                    leanh::lean_dec_ref_known(v_a_6784_, 0);
                    leanh::lean_dec_ref(v_x_6746_);
                    if v_contextDependent_6779_ == 0 {
                        v___y_6789_ = v___x_6757_;
                        state = 6;
                        continue;
                    } else {
                        v___y_6789_ = v_contextDependent_6779_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6786_);
                    leanh::lean_del_object(v___x_6781_);
                    v_e_x27_6796_ = leanh::lean_ctor_get(v_a_6784_, 0);
                    v_proof_6797_ = leanh::lean_ctor_get(v_a_6784_, 1);
                    v_isSharedCheck_6823_ = (!leanh::lean_is_exclusive(v_a_6784_)) as u8;
                    if v_isSharedCheck_6823_ == 0 {
                        v___x_6799_ = v_a_6784_;
                        v_isShared_6800_ = v_isSharedCheck_6823_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_proof_6797_);
                        leanh::lean_inc(v_e_x27_6796_);
                        leanh::lean_dec(v_a_6784_);
                        v___x_6799_ = leanh::lean_box(0);
                        v_isShared_6800_ = v_isSharedCheck_6823_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_6782_ == 0 {
                    v___x_6791_ = v___x_6781_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6795_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6795_, 0, v_e_x27_6777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6795_, 1, v_proof_6778_);
                    v___x_6791_ = v_reuseFailAlloc_6795_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(
                    v___x_6791_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_6757_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6791_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_6789_,
                );
                if v_isShared_6787_ == 0 {
                    leanh::lean_ctor_set(v___x_6786_, 0, v___x_6791_);
                    v___x_6793_ = v___x_6786_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6794_, 0, v___x_6791_);
                    v___x_6793_ = v_reuseFailAlloc_6794_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6793_;
            }
            9 => {
                leanh::lean_inc_ref(v_e_x27_6796_);
                v___x_6801_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                    v_x_6746_,
                    v_e_x27_6777_,
                    v_proof_6778_,
                    v_e_x27_6796_,
                    v_proof_6797_,
                    v_a_6751_,
                    v_a_6752_,
                    v_a_6753_,
                    v_a_6754_,
                    v_a_6755_,
                );
                if leanh::lean_obj_tag(v___x_6801_) == 0 {
                    v_a_6802_ = leanh::lean_ctor_get(v___x_6801_, 0);
                    v_isSharedCheck_6814_ = (!leanh::lean_is_exclusive(v___x_6801_)) as u8;
                    if v_isSharedCheck_6814_ == 0 {
                        v___x_6804_ = v___x_6801_;
                        v_isShared_6805_ = v_isSharedCheck_6814_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6802_);
                        leanh::lean_dec(v___x_6801_);
                        v___x_6804_ = leanh::lean_box(0);
                        v_isShared_6805_ = v_isSharedCheck_6814_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6799_);
                    leanh::lean_dec_ref(v_e_x27_6796_);
                    v_a_6815_ = leanh::lean_ctor_get(v___x_6801_, 0);
                    v_isSharedCheck_6822_ = (!leanh::lean_is_exclusive(v___x_6801_)) as u8;
                    if v_isSharedCheck_6822_ == 0 {
                        v___x_6817_ = v___x_6801_;
                        v_isShared_6818_ = v_isSharedCheck_6822_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6815_);
                        leanh::lean_dec(v___x_6801_);
                        v___x_6817_ = leanh::lean_box(0);
                        v_isShared_6818_ = v_isSharedCheck_6822_;
                        state = 14;
                        continue;
                    }
                }
            }
            10 => {
                if v_contextDependent_6779_ == 0 {
                    v___y_6807_ = v___x_6757_;
                    state = 11;
                    continue;
                } else {
                    v___y_6807_ = v_contextDependent_6779_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_6800_ == 0 {
                    leanh::lean_ctor_set(v___x_6799_, 1, v_a_6802_);
                    v___x_6809_ = v___x_6799_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6813_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6813_, 0, v_e_x27_6796_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6813_, 1, v_a_6802_);
                    v___x_6809_ = v_reuseFailAlloc_6813_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                leanh::lean_ctor_set_uint8(
                    v___x_6809_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_6757_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6809_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_6807_,
                );
                if v_isShared_6805_ == 0 {
                    leanh::lean_ctor_set(v___x_6804_, 0, v___x_6809_);
                    v___x_6811_ = v___x_6804_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6812_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6812_, 0, v___x_6809_);
                    v___x_6811_ = v_reuseFailAlloc_6812_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6811_;
            }
            14 => {
                if v_isShared_6818_ == 0 {
                    v___x_6820_ = v___x_6817_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_a_6815_);
                    v___x_6820_ = v_reuseFailAlloc_6821_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6820_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed(
    mut v_x_6826_: *mut leanh::LeanObject,
    mut v_a_6827_: *mut leanh::LeanObject,
    mut v_a_6828_: *mut leanh::LeanObject,
    mut v_a_6829_: *mut leanh::LeanObject,
    mut v_a_6830_: *mut leanh::LeanObject,
    mut v_a_6831_: *mut leanh::LeanObject,
    mut v_a_6832_: *mut leanh::LeanObject,
    mut v_a_6833_: *mut leanh::LeanObject,
    mut v_a_6834_: *mut leanh::LeanObject,
    mut v_a_6835_: *mut leanh::LeanObject,
    mut v_a_6836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6837_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec(
            v_x_6826_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_, v_a_6831_, v_a_6832_, v_a_6833_,
            v_a_6834_, v_a_6835_,
        );
    leanh::lean_dec(v_a_6835_);
    leanh::lean_dec_ref(v_a_6834_);
    leanh::lean_dec(v_a_6833_);
    leanh::lean_dec_ref(v_a_6832_);
    leanh::lean_dec(v_a_6831_);
    leanh::lean_dec_ref(v_a_6830_);
    leanh::lean_dec(v_a_6829_);
    leanh::lean_dec_ref(v_a_6828_);
    leanh::lean_dec(v_a_6827_);
    return v_res_6837_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_()
-> *mut leanh::LeanObject {
    let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6860_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_;
    v___x_6861_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__5_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_;
    v___x_6862_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_6863_ =
        l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(v___x_6860_, v___x_6861_, v___x_6862_);
    return v___x_6863_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17____boxed(
    mut v_a_6864_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6865_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_();
    return v_res_6865_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_()
-> *mut leanh::LeanObject {
    let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: u8 = 0;
    let mut v___x_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6867_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77___closed__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_;
    v___x_6868_ = 0;
    v___x_6869_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___boxed as *mut core::ffi::c_void, 11, 0);
    v___x_6870_ =
        l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(v___x_6867_, v___x_6868_, v___x_6869_);
    return v___x_6870_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19____boxed(
    mut v_a_6871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6872_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_();
    return v_res_6872_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(
    mut v_appFn_6874_: *mut leanh::LeanObject,
    mut v_e_6875_: *mut leanh::LeanObject,
    mut v_a_6876_: *mut leanh::LeanObject,
    mut v_a_6877_: *mut leanh::LeanObject,
    mut v_a_6878_: *mut leanh::LeanObject,
    mut v_a_6879_: *mut leanh::LeanObject,
    mut v_a_6880_: *mut leanh::LeanObject,
    mut v_a_6881_: *mut leanh::LeanObject,
    mut v_a_6882_: *mut leanh::LeanObject,
    mut v_a_6883_: *mut leanh::LeanObject,
    mut v_a_6884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6893_: u8 = 0;
    let mut v___x_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6886_ = l_Lean_Meta_Tactic_Cbv_getMatchTheorems(
                    v_appFn_6874_,
                    v_a_6881_,
                    v_a_6882_,
                    v_a_6883_,
                    v_a_6884_,
                );
                if leanh::lean_obj_tag(v___x_6886_) == 0 {
                    v_a_6887_ = leanh::lean_ctor_get(v___x_6886_, 0);
                    leanh::lean_inc(v_a_6887_);
                    leanh::lean_dec_ref_known(v___x_6886_, 1);
                    v___x_6888_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___closed__0;
                    v___x_6889_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(
                        v_a_6887_,
                        v___x_6888_,
                        v_e_6875_,
                        v_a_6876_,
                        v_a_6877_,
                        v_a_6878_,
                        v_a_6879_,
                        v_a_6880_,
                        v_a_6881_,
                        v_a_6882_,
                        v_a_6883_,
                        v_a_6884_,
                    );
                    leanh::lean_dec(v_a_6887_);
                    return v___x_6889_;
                } else {
                    leanh::lean_dec_ref(v_e_6875_);
                    v_a_6890_ = leanh::lean_ctor_get(v___x_6886_, 0);
                    v_isSharedCheck_6897_ = (!leanh::lean_is_exclusive(v___x_6886_)) as u8;
                    if v_isSharedCheck_6897_ == 0 {
                        v___x_6892_ = v___x_6886_;
                        v_isShared_6893_ = v_isSharedCheck_6897_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6890_);
                        leanh::lean_dec(v___x_6886_);
                        v___x_6892_ = leanh::lean_box(0);
                        v_isShared_6893_ = v_isSharedCheck_6897_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6893_ == 0 {
                    v___x_6895_ = v___x_6892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6896_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6896_, 0, v_a_6890_);
                    v___x_6895_ = v_reuseFailAlloc_6896_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations___boxed(
    mut v_appFn_6898_: *mut leanh::LeanObject,
    mut v_e_6899_: *mut leanh::LeanObject,
    mut v_a_6900_: *mut leanh::LeanObject,
    mut v_a_6901_: *mut leanh::LeanObject,
    mut v_a_6902_: *mut leanh::LeanObject,
    mut v_a_6903_: *mut leanh::LeanObject,
    mut v_a_6904_: *mut leanh::LeanObject,
    mut v_a_6905_: *mut leanh::LeanObject,
    mut v_a_6906_: *mut leanh::LeanObject,
    mut v_a_6907_: *mut leanh::LeanObject,
    mut v_a_6908_: *mut leanh::LeanObject,
    mut v_a_6909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6910_ =
        l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(
            v_appFn_6898_,
            v_e_6899_,
            v_a_6900_,
            v_a_6901_,
            v_a_6902_,
            v_a_6903_,
            v_a_6904_,
            v_a_6905_,
            v_a_6906_,
            v_a_6907_,
            v_a_6908_,
        );
    leanh::lean_dec(v_a_6908_);
    leanh::lean_dec_ref(v_a_6907_);
    leanh::lean_dec(v_a_6906_);
    leanh::lean_dec_ref(v_a_6905_);
    leanh::lean_dec(v_a_6904_);
    leanh::lean_dec_ref(v_a_6903_);
    leanh::lean_dec(v_a_6902_);
    leanh::lean_dec_ref(v_a_6901_);
    leanh::lean_dec(v_a_6900_);
    return v_res_6910_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(
    mut v_declName_6911_: *mut leanh::LeanObject,
    mut v___y_6912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6914_ = lean_st_ref_get(v___y_6912_);
    v_env_6915_ = leanh::lean_ctor_get(v___x_6914_, 0);
    leanh::lean_inc_ref(v_env_6915_);
    leanh::lean_dec(v___x_6914_);
    v___x_6916_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_6915_, v_declName_6911_);
    v___x_6917_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6917_, 0, v___x_6916_);
    return v___x_6917_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg___boxed(
    mut v_declName_6918_: *mut leanh::LeanObject,
    mut v___y_6919_: *mut leanh::LeanObject,
    mut v___y_6920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6921_ =
        l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(
            v_declName_6918_,
            v___y_6919_,
        );
    leanh::lean_dec(v___y_6919_);
    return v_res_6921_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(
    mut v_declName_6922_: *mut leanh::LeanObject,
    mut v___y_6923_: *mut leanh::LeanObject,
    mut v___y_6924_: *mut leanh::LeanObject,
    mut v___y_6925_: *mut leanh::LeanObject,
    mut v___y_6926_: *mut leanh::LeanObject,
    mut v___y_6927_: *mut leanh::LeanObject,
    mut v___y_6928_: *mut leanh::LeanObject,
    mut v___y_6929_: *mut leanh::LeanObject,
    mut v___y_6930_: *mut leanh::LeanObject,
    mut v___y_6931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6933_ =
        l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(
            v_declName_6922_,
            v___y_6931_,
        );
    return v___x_6933_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___boxed(
    mut v_declName_6934_: *mut leanh::LeanObject,
    mut v___y_6935_: *mut leanh::LeanObject,
    mut v___y_6936_: *mut leanh::LeanObject,
    mut v___y_6937_: *mut leanh::LeanObject,
    mut v___y_6938_: *mut leanh::LeanObject,
    mut v___y_6939_: *mut leanh::LeanObject,
    mut v___y_6940_: *mut leanh::LeanObject,
    mut v___y_6941_: *mut leanh::LeanObject,
    mut v___y_6942_: *mut leanh::LeanObject,
    mut v___y_6943_: *mut leanh::LeanObject,
    mut v___y_6944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6945_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0(
        v_declName_6934_,
        v___y_6935_,
        v___y_6936_,
        v___y_6937_,
        v___y_6938_,
        v___y_6939_,
        v___y_6940_,
        v___y_6941_,
        v___y_6942_,
        v___y_6943_,
    );
    leanh::lean_dec(v___y_6943_);
    leanh::lean_dec_ref(v___y_6942_);
    leanh::lean_dec(v___y_6941_);
    leanh::lean_dec_ref(v___y_6940_);
    leanh::lean_dec(v___y_6939_);
    leanh::lean_dec_ref(v___y_6938_);
    leanh::lean_dec(v___y_6937_);
    leanh::lean_dec_ref(v___y_6936_);
    leanh::lean_dec(v___y_6935_);
    return v_res_6945_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6952_ = l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1;
    v___x_6953_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__4;
    v___x_6954_ = l_Lean_Name_append(v___x_6953_, v___x_6952_);
    return v___x_6954_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_6956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6956_ = l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__3;
    v___x_6957_ = l_Lean_stringToMessageData(v___x_6956_);
    return v___x_6957_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_6959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6959_ = l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__5;
    v___x_6960_ = l_Lean_stringToMessageData(v___x_6959_);
    return v___x_6960_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_tryMatcher(
    mut v_e_6961_: *mut leanh::LeanObject,
    mut v_a_6962_: *mut leanh::LeanObject,
    mut v_a_6963_: *mut leanh::LeanObject,
    mut v_a_6964_: *mut leanh::LeanObject,
    mut v_a_6965_: *mut leanh::LeanObject,
    mut v_a_6966_: *mut leanh::LeanObject,
    mut v_a_6967_: *mut leanh::LeanObject,
    mut v_a_6968_: *mut leanh::LeanObject,
    mut v_a_6969_: *mut leanh::LeanObject,
    mut v_a_6970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6972_: u8 = 0;
    let mut v___x_6973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6980_: u8 = 0;
    let mut v_a_6982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6985_: u8 = 0;
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: u8 = 0;
    let mut v___x_6994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7010_: u8 = 0;
    let mut v___x_7012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7014_: u8 = 0;
    let mut v_unused_7015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7019_: u8 = 0;
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7023_: u8 = 0;
    let mut v___y_7025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_7027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7034_: u8 = 0;
    let mut v___x_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_7040_: u8 = 0;
    let mut v_contextDependent_7041_: u8 = 0;
    let mut v___x_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: u8 = 0;
    let mut v_e_x27_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7053_: u8 = 0;
    let mut v_val_7054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_7056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_7062_: u8 = 0;
    let mut v_contextDependent_7063_: u8 = 0;
    let mut v___x_7064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7067_: u8 = 0;
    let mut v___x_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7070_: u8 = 0;
    let mut v___x_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7075_: u8 = 0;
    let mut v_unused_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_7077_: u8 = 0;
    let mut v_contextDependent_7078_: u8 = 0;
    let mut v_done_7079_: u8 = 0;
    let mut v_e_x27_7080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_contextDependent_7082_: u8 = 0;
    let mut v___x_7084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7085_: u8 = 0;
    let mut v___x_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_7088_: u8 = 0;
    let mut v_contextDependent_7089_: u8 = 0;
    let mut v___y_7091_: u8 = 0;
    let mut v___x_7093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_7095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_7096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_done_7097_: u8 = 0;
    let mut v_contextDependent_7098_: u8 = 0;
    let mut v___x_7100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7101_: u8 = 0;
    let mut v___x_7102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7105_: u8 = 0;
    let mut v___x_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7112_: u8 = 0;
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7116_: u8 = 0;
    let mut v_isSharedCheck_7117_: u8 = 0;
    let mut v_isSharedCheck_7118_: u8 = 0;
    let mut v___x_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7123_: u8 = 0;
    let mut v_isSharedCheck_7124_: u8 = 0;
    let mut v___x_7125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6972_ = l_Lean_Expr_isApp(v_e_6961_);
                if v___x_6972_ == 0 {
                    leanh::lean_dec_ref(v_e_6961_);
                    v___x_6973_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    leanh::lean_ctor_set_uint8(v___x_6973_, 0 as u32, v___x_6972_);
                    leanh::lean_ctor_set_uint8(v___x_6973_, 1 as u32, v___x_6972_);
                    v___x_6974_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6974_, 0, v___x_6973_);
                    return v___x_6974_;
                } else {
                    v___x_6975_ = l_Lean_Expr_getAppFn(v_e_6961_);
                    v___x_6976_ = l_Lean_Expr_constName_x3f(v___x_6975_);
                    leanh::lean_dec_ref(v___x_6975_);
                    if leanh::lean_obj_tag(v___x_6976_) == 1 {
                        v_val_6977_ = leanh::lean_ctor_get(v___x_6976_, 0);
                        v_isSharedCheck_7124_ =
                            (!leanh::lean_is_exclusive(v___x_6976_)) as u8;
                        if v_isSharedCheck_7124_ == 0 {
                            v___x_6979_ = v___x_6976_;
                            v_isShared_6980_ = v_isSharedCheck_7124_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_6977_);
                            leanh::lean_dec(v___x_6976_);
                            v___x_6979_ = leanh::lean_box(0);
                            v_isShared_6980_ = v_isSharedCheck_7124_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_6976_);
                        leanh::lean_dec_ref(v_e_6961_);
                        v___x_7125_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10;
                        v___x_7126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_7126_, 0, v___x_7125_);
                        return v___x_7126_;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_val_6977_);
                v___x_7049_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_Tactic_Cbv_tryMatcher_spec__0___redArg(v_val_6977_, v_a_6970_);
                v_a_7050_ = leanh::lean_ctor_get(v___x_7049_, 0);
                v_isSharedCheck_7123_ = (!leanh::lean_is_exclusive(v___x_7049_)) as u8;
                if v_isSharedCheck_7123_ == 0 {
                    v___x_7052_ = v___x_7049_;
                    v_isShared_7053_ = v_isSharedCheck_7123_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7050_);
                    leanh::lean_dec(v___x_7049_);
                    v___x_7052_ = leanh::lean_box(0);
                    v_isShared_7053_ = v_isSharedCheck_7123_;
                    state = 14;
                    continue;
                }
            }
            2 => {
                v_options_6984_ = leanh::lean_ctor_get(v_a_6969_, 2);
                v_hasTrace_6985_ = leanh::lean_ctor_get_uint8(
                    v_options_6984_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_6985_ == 0 {
                    leanh::lean_dec_ref(v_e_x27_6983_);
                    leanh::lean_dec(v_val_6977_);
                    leanh::lean_dec_ref(v_e_6961_);
                    if v_isShared_6980_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6979_, 0);
                        leanh::lean_ctor_set(v___x_6979_, 0, v_a_6982_);
                        v___x_6987_ = v___x_6979_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6988_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6988_, 0, v_a_6982_);
                        v___x_6987_ = v_reuseFailAlloc_6988_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_inheritedTraceOptions_6989_ = leanh::lean_ctor_get(v_a_6969_, 13);
                    v___x_6990_ = l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__1;
                    v___x_6991_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2_once),
                        _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__2,
                    );
                    v___x_6992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6989_,
                        v_options_6984_,
                        v___x_6991_,
                    );
                    if v___x_6992_ == 0 {
                        leanh::lean_dec_ref(v_e_x27_6983_);
                        leanh::lean_dec(v_val_6977_);
                        leanh::lean_dec_ref(v_e_6961_);
                        if v_isShared_6980_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_6979_, 0);
                            leanh::lean_ctor_set(v___x_6979_, 0, v_a_6982_);
                            v___x_6994_ = v___x_6979_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_6995_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6995_, 0, v_a_6982_);
                            v___x_6994_ = v_reuseFailAlloc_6995_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6979_);
                        v___x_6996_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__4,
                        );
                        v___x_6997_ = l_Lean_MessageData_ofName(v_val_6977_);
                        v___x_6998_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6998_, 0, v___x_6996_);
                        leanh::lean_ctor_set(v___x_6998_, 1, v___x_6997_);
                        v___x_6999_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_tryMatcher___closed__6,
                        );
                        v___x_7000_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7000_, 0, v___x_6998_);
                        leanh::lean_ctor_set(v___x_7000_, 1, v___x_6999_);
                        v___x_7001_ = l_Lean_indentExpr(v_e_6961_);
                        v___x_7002_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7002_, 0, v___x_7000_);
                        leanh::lean_ctor_set(v___x_7002_, 1, v___x_7001_);
                        v___x_7003_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__9,
                        );
                        v___x_7004_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7004_, 0, v___x_7002_);
                        leanh::lean_ctor_set(v___x_7004_, 1, v___x_7003_);
                        v___x_7005_ = l_Lean_indentExpr(v_e_x27_6983_);
                        v___x_7006_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7006_, 0, v___x_7004_);
                        leanh::lean_ctor_set(v___x_7006_, 1, v___x_7005_);
                        v___x_7007_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_reduceRecMatcher_spec__0___redArg(v___x_6990_, v___x_7006_, v_a_6967_, v_a_6968_, v_a_6969_, v_a_6970_);
                        if leanh::lean_obj_tag(v___x_7007_) == 0 {
                            v_isSharedCheck_7014_ =
                                (!leanh::lean_is_exclusive(v___x_7007_)) as u8;
                            if v_isSharedCheck_7014_ == 0 {
                                v_unused_7015_ = leanh::lean_ctor_get(v___x_7007_, 0);
                                leanh::lean_dec(v_unused_7015_);
                                v___x_7009_ = v___x_7007_;
                                v_isShared_7010_ = v_isSharedCheck_7014_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_7007_);
                                v___x_7009_ = leanh::lean_box(0);
                                v_isShared_7010_ = v_isSharedCheck_7014_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_a_6982_);
                            v_a_7016_ = leanh::lean_ctor_get(v___x_7007_, 0);
                            v_isSharedCheck_7023_ =
                                (!leanh::lean_is_exclusive(v___x_7007_)) as u8;
                            if v_isSharedCheck_7023_ == 0 {
                                v___x_7018_ = v___x_7007_;
                                v_isShared_7019_ = v_isSharedCheck_7023_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7016_);
                                leanh::lean_dec(v___x_7007_);
                                v___x_7018_ = leanh::lean_box(0);
                                v_isShared_7019_ = v_isSharedCheck_7023_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_6987_;
            }
            4 => {
                return v___x_6994_;
            }
            5 => {
                if v_isShared_7010_ == 0 {
                    leanh::lean_ctor_set(v___x_7009_, 0, v_a_6982_);
                    v___x_7012_ = v___x_7009_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7013_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7013_, 0, v_a_6982_);
                    v___x_7012_ = v_reuseFailAlloc_7013_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7012_;
            }
            7 => {
                if v_isShared_7019_ == 0 {
                    v___x_7021_ = v___x_7018_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7022_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7022_, 0, v_a_7016_);
                    v___x_7021_ = v_reuseFailAlloc_7022_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7021_;
            }
            9 => {
                if leanh::lean_obj_tag(v_a_7026_) == 1 {
                    leanh::lean_dec_ref(v___y_7025_);
                    v_e_x27_7027_ = leanh::lean_ctor_get(v_a_7026_, 0);
                    leanh::lean_inc_ref(v_e_x27_7027_);
                    v_a_6982_ = v_a_7026_;
                    v_e_x27_6983_ = v_e_x27_7027_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_a_7026_);
                    leanh::lean_del_object(v___x_6979_);
                    leanh::lean_dec(v_val_6977_);
                    leanh::lean_dec_ref(v_e_6961_);
                    return v___y_7025_;
                }
            }
            10 => {
                if leanh::lean_obj_tag(v___y_7029_) == 0 {
                    v_a_7030_ = leanh::lean_ctor_get(v___y_7029_, 0);
                    leanh::lean_inc(v_a_7030_);
                    v___y_7025_ = v___y_7029_;
                    v_a_7026_ = v_a_7030_;
                    state = 9;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6979_);
                    leanh::lean_dec(v_val_6977_);
                    leanh::lean_dec_ref(v_e_6961_);
                    return v___y_7029_;
                }
            }
            11 => {
                leanh::lean_dec_ref(v___y_7033_);
                v___x_7035_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_7032_);
                leanh::lean_inc_ref(v___x_7035_);
                v___x_7036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7036_, 0, v___x_7035_);
                v___y_7025_ = v___x_7036_;
                v_a_7026_ = v___x_7035_;
                state = 9;
                continue;
            }
            12 => {
                if leanh::lean_obj_tag(v_a_7039_) == 0 {
                    v_done_7040_ = leanh::lean_ctor_get_uint8(v_a_7039_, 0 as u32);
                    if v_done_7040_ == 0 {
                        leanh::lean_dec_ref(v___y_7038_);
                        v_contextDependent_7041_ =
                            leanh::lean_ctor_get_uint8(v_a_7039_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_7039_, 0);
                        leanh::lean_inc_ref(v_e_6961_);
                        v___x_7042_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(
                            v_e_6961_, v_a_6962_, v_a_6963_, v_a_6964_, v_a_6965_, v_a_6966_,
                            v_a_6967_, v_a_6968_, v_a_6969_, v_a_6970_,
                        );
                        if leanh::lean_obj_tag(v___x_7042_) == 0 {
                            if v_contextDependent_7041_ == 0 {
                                v___y_7029_ = v___x_7042_;
                                state = 10;
                                continue;
                            } else {
                                v_a_7043_ = leanh::lean_ctor_get(v___x_7042_, 0);
                                leanh::lean_inc(v_a_7043_);
                                v___x_7044_ = 0;
                                v___y_7032_ = v_a_7043_;
                                v___y_7033_ = v___x_7042_;
                                v___y_7034_ = v___x_7044_;
                                state = 11;
                                continue;
                            }
                        } else {
                            v___y_7029_ = v___x_7042_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_a_7039_, 0);
                        leanh::lean_del_object(v___x_6979_);
                        leanh::lean_dec(v_val_6977_);
                        leanh::lean_dec_ref(v_e_6961_);
                        return v___y_7038_;
                    }
                } else {
                    leanh::lean_dec_ref(v___y_7038_);
                    v_e_x27_7045_ = leanh::lean_ctor_get(v_a_7039_, 0);
                    leanh::lean_inc_ref(v_e_x27_7045_);
                    v_a_6982_ = v_a_7039_;
                    v_e_x27_6983_ = v_e_x27_7045_;
                    state = 2;
                    continue;
                }
            }
            13 => {
                if leanh::lean_obj_tag(v___y_7047_) == 0 {
                    v_a_7048_ = leanh::lean_ctor_get(v___y_7047_, 0);
                    leanh::lean_inc(v_a_7048_);
                    v___y_7038_ = v___y_7047_;
                    v_a_7039_ = v_a_7048_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_del_object(v___x_6979_);
                    leanh::lean_dec(v_val_6977_);
                    leanh::lean_dec_ref(v_e_6961_);
                    return v___y_7047_;
                }
            }
            14 => {
                if leanh::lean_obj_tag(v_a_7050_) == 1 {
                    leanh::lean_del_object(v___x_7052_);
                    v_val_7054_ = leanh::lean_ctor_get(v_a_7050_, 0);
                    leanh::lean_inc(v_val_7054_);
                    leanh::lean_dec_ref_known(v_a_7050_, 1);
                    v_numParams_7055_ = leanh::lean_ctor_get(v_val_7054_, 0);
                    leanh::lean_inc(v_numParams_7055_);
                    v_numDiscrs_7056_ = leanh::lean_ctor_get(v_val_7054_, 1);
                    leanh::lean_inc(v_numDiscrs_7056_);
                    leanh::lean_dec(v_val_7054_);
                    v___x_7057_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7058_ = lean_nat_add(v_numParams_7055_, v___x_7057_);
                    leanh::lean_dec(v_numParams_7055_);
                    v___x_7059_ = lean_nat_add(v___x_7058_, v_numDiscrs_7056_);
                    leanh::lean_dec(v_numDiscrs_7056_);
                    leanh::lean_inc_ref(v_e_6961_);
                    v___x_7060_ = l_Lean_Meta_Sym_Simp_simpAppArgRange(
                        v_e_6961_,
                        v___x_7058_,
                        v___x_7059_,
                        v_a_6962_,
                        v_a_6963_,
                        v_a_6964_,
                        v_a_6965_,
                        v_a_6966_,
                        v_a_6967_,
                        v_a_6968_,
                        v_a_6969_,
                        v_a_6970_,
                    );
                    leanh::lean_dec(v___x_7059_);
                    leanh::lean_dec(v___x_7058_);
                    if leanh::lean_obj_tag(v___x_7060_) == 0 {
                        v_a_7061_ = leanh::lean_ctor_get(v___x_7060_, 0);
                        leanh::lean_inc(v_a_7061_);
                        if leanh::lean_obj_tag(v_a_7061_) == 0 {
                            v_done_7062_ = leanh::lean_ctor_get_uint8(v_a_7061_, 0 as u32);
                            if v_done_7062_ == 0 {
                                leanh::lean_dec_ref_known(v___x_7060_, 1);
                                v_contextDependent_7063_ =
                                    leanh::lean_ctor_get_uint8(v_a_7061_, 1 as u32);
                                leanh::lean_dec_ref_known(v_a_7061_, 0);
                                leanh::lean_inc_ref(v_e_6961_);
                                leanh::lean_inc(v_val_6977_);
                                v___x_7064_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_6977_, v_e_6961_, v_a_6962_, v_a_6963_, v_a_6964_, v_a_6965_, v_a_6966_, v_a_6967_, v_a_6968_, v_a_6969_, v_a_6970_);
                                if leanh::lean_obj_tag(v___x_7064_) == 0 {
                                    v_a_7065_ = leanh::lean_ctor_get(v___x_7064_, 0);
                                    leanh::lean_inc(v_a_7065_);
                                    if v_contextDependent_7063_ == 0 {
                                        leanh::lean_dec(v_a_7065_);
                                        v___y_7047_ = v___x_7064_;
                                        state = 13;
                                        continue;
                                    } else {
                                        if leanh::lean_obj_tag(v_a_7065_) == 0 {
                                            v_contextDependent_7077_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v_a_7065_, 1 as u32,
                                                );
                                            v___y_7067_ = v_contextDependent_7077_;
                                            state = 15;
                                            continue;
                                        } else {
                                            v_contextDependent_7078_ =
                                                leanh::lean_ctor_get_uint8(
                                                    v_a_7065_,
                                                    (core::mem::size_of::<
                                                        *mut leanh::LeanObject,
                                                    >(
                                                    ) * 2
                                                        + 1)
                                                        as u32,
                                                );
                                            v___y_7067_ = v_contextDependent_7078_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                } else {
                                    v___y_7047_ = v___x_7064_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_a_7061_, 0);
                                v___y_7047_ = v___x_7060_;
                                state = 13;
                                continue;
                            }
                        } else {
                            v_done_7079_ = leanh::lean_ctor_get_uint8(
                                v_a_7061_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            );
                            if v_done_7079_ == 0 {
                                leanh::lean_dec_ref_known(v___x_7060_, 1);
                                v_e_x27_7080_ = leanh::lean_ctor_get(v_a_7061_, 0);
                                v_proof_7081_ = leanh::lean_ctor_get(v_a_7061_, 1);
                                v_contextDependent_7082_ = leanh::lean_ctor_get_uint8(
                                    v_a_7061_,
                                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1)
                                        as u32,
                                );
                                v_isSharedCheck_7118_ =
                                    (!leanh::lean_is_exclusive(v_a_7061_)) as u8;
                                if v_isSharedCheck_7118_ == 0 {
                                    v___x_7084_ = v_a_7061_;
                                    v_isShared_7085_ = v_isSharedCheck_7118_;
                                    state = 18;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_proof_7081_);
                                    leanh::lean_inc(v_e_x27_7080_);
                                    leanh::lean_dec(v_a_7061_);
                                    v___x_7084_ = leanh::lean_box(0);
                                    v_isShared_7085_ = v_isSharedCheck_7118_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_a_7061_, 2);
                                v___y_7047_ = v___x_7060_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        v___y_7047_ = v___x_7060_;
                        state = 13;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7050_);
                    leanh::lean_del_object(v___x_6979_);
                    leanh::lean_dec(v_val_6977_);
                    leanh::lean_dec_ref(v_e_6961_);
                    v___x_7119_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher___closed__10;
                    if v_isShared_7053_ == 0 {
                        leanh::lean_ctor_set(v___x_7052_, 0, v___x_7119_);
                        v___x_7121_ = v___x_7052_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_7122_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7122_, 0, v___x_7119_);
                        v___x_7121_ = v_reuseFailAlloc_7122_;
                        state = 26;
                        continue;
                    }
                }
            }
            15 => {
                if v___y_7067_ == 0 {
                    v_isSharedCheck_7075_ = (!leanh::lean_is_exclusive(v___x_7064_)) as u8;
                    if v_isSharedCheck_7075_ == 0 {
                        v_unused_7076_ = leanh::lean_ctor_get(v___x_7064_, 0);
                        leanh::lean_dec(v_unused_7076_);
                        v___x_7069_ = v___x_7064_;
                        v_isShared_7070_ = v_isSharedCheck_7075_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_7064_);
                        v___x_7069_ = leanh::lean_box(0);
                        v_isShared_7070_ = v_isSharedCheck_7075_;
                        state = 16;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7065_);
                    v___y_7047_ = v___x_7064_;
                    state = 13;
                    continue;
                }
            }
            16 => {
                v___x_7071_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_7065_);
                leanh::lean_inc_ref(v___x_7071_);
                if v_isShared_7070_ == 0 {
                    leanh::lean_ctor_set(v___x_7069_, 0, v___x_7071_);
                    v___x_7073_ = v___x_7069_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7074_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7074_, 0, v___x_7071_);
                    v___x_7073_ = v_reuseFailAlloc_7074_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___y_7038_ = v___x_7073_;
                v_a_7039_ = v___x_7071_;
                state = 12;
                continue;
            }
            18 => {
                leanh::lean_inc_ref(v_e_x27_7080_);
                leanh::lean_inc(v_val_6977_);
                v___x_7086_ = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_tryMatchEquations(v_val_6977_, v_e_x27_7080_, v_a_6962_, v_a_6963_, v_a_6964_, v_a_6965_, v_a_6966_, v_a_6967_, v_a_6968_, v_a_6969_, v_a_6970_);
                if leanh::lean_obj_tag(v___x_7086_) == 0 {
                    v_a_7087_ = leanh::lean_ctor_get(v___x_7086_, 0);
                    leanh::lean_inc(v_a_7087_);
                    leanh::lean_dec_ref_known(v___x_7086_, 1);
                    if leanh::lean_obj_tag(v_a_7087_) == 0 {
                        v_done_7088_ = leanh::lean_ctor_get_uint8(v_a_7087_, 0 as u32);
                        v_contextDependent_7089_ =
                            leanh::lean_ctor_get_uint8(v_a_7087_, 1 as u32);
                        leanh::lean_dec_ref_known(v_a_7087_, 0);
                        if v_contextDependent_7082_ == 0 {
                            v___y_7091_ = v_contextDependent_7089_;
                            state = 19;
                            continue;
                        } else {
                            v___y_7091_ = v_contextDependent_7082_;
                            state = 19;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_7084_);
                        v_e_x27_7095_ = leanh::lean_ctor_get(v_a_7087_, 0);
                        v_proof_7096_ = leanh::lean_ctor_get(v_a_7087_, 1);
                        v_done_7097_ = leanh::lean_ctor_get_uint8(
                            v_a_7087_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v_contextDependent_7098_ = leanh::lean_ctor_get_uint8(
                            v_a_7087_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                        );
                        v_isSharedCheck_7117_ = (!leanh::lean_is_exclusive(v_a_7087_)) as u8;
                        if v_isSharedCheck_7117_ == 0 {
                            v___x_7100_ = v_a_7087_;
                            v_isShared_7101_ = v_isSharedCheck_7117_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_proof_7096_);
                            leanh::lean_inc(v_e_x27_7095_);
                            leanh::lean_dec(v_a_7087_);
                            v___x_7100_ = leanh::lean_box(0);
                            v_isShared_7101_ = v_isSharedCheck_7117_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7084_);
                    leanh::lean_dec_ref(v_proof_7081_);
                    leanh::lean_dec_ref(v_e_x27_7080_);
                    v___y_7047_ = v___x_7086_;
                    state = 13;
                    continue;
                }
            }
            19 => {
                leanh::lean_inc_ref(v_e_x27_7080_);
                if v_isShared_7085_ == 0 {
                    v___x_7093_ = v___x_7084_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7094_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7094_, 0, v_e_x27_7080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7094_, 1, v_proof_7081_);
                    v___x_7093_ = v_reuseFailAlloc_7094_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                leanh::lean_ctor_set_uint8(
                    v___x_7093_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_done_7088_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7093_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_7091_,
                );
                v_a_6982_ = v___x_7093_;
                v_e_x27_6983_ = v_e_x27_7080_;
                state = 2;
                continue;
            }
            21 => {
                leanh::lean_inc_ref(v_e_x27_7095_);
                leanh::lean_inc_ref(v_e_6961_);
                v___x_7102_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(
                    v_e_6961_,
                    v_e_x27_7080_,
                    v_proof_7081_,
                    v_e_x27_7095_,
                    v_proof_7096_,
                    v_a_6966_,
                    v_a_6967_,
                    v_a_6968_,
                    v_a_6969_,
                    v_a_6970_,
                );
                if leanh::lean_obj_tag(v___x_7102_) == 0 {
                    v_a_7103_ = leanh::lean_ctor_get(v___x_7102_, 0);
                    leanh::lean_inc(v_a_7103_);
                    leanh::lean_dec_ref_known(v___x_7102_, 1);
                    if v_contextDependent_7082_ == 0 {
                        v___y_7105_ = v_contextDependent_7098_;
                        state = 22;
                        continue;
                    } else {
                        v___y_7105_ = v_contextDependent_7082_;
                        state = 22;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7100_);
                    leanh::lean_dec_ref(v_e_x27_7095_);
                    leanh::lean_del_object(v___x_6979_);
                    leanh::lean_dec(v_val_6977_);
                    leanh::lean_dec_ref(v_e_6961_);
                    v_a_7109_ = leanh::lean_ctor_get(v___x_7102_, 0);
                    v_isSharedCheck_7116_ = (!leanh::lean_is_exclusive(v___x_7102_)) as u8;
                    if v_isSharedCheck_7116_ == 0 {
                        v___x_7111_ = v___x_7102_;
                        v_isShared_7112_ = v_isSharedCheck_7116_;
                        state = 24;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7109_);
                        leanh::lean_dec(v___x_7102_);
                        v___x_7111_ = leanh::lean_box(0);
                        v_isShared_7112_ = v_isSharedCheck_7116_;
                        state = 24;
                        continue;
                    }
                }
            }
            22 => {
                leanh::lean_inc_ref(v_e_x27_7095_);
                if v_isShared_7101_ == 0 {
                    leanh::lean_ctor_set(v___x_7100_, 1, v_a_7103_);
                    v___x_7107_ = v___x_7100_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7108_ = leanh::lean_alloc_ctor(1, 2, (2) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7108_, 0, v_e_x27_7095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7108_, 1, v_a_7103_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7108_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_done_7097_,
                    );
                    v___x_7107_ = v_reuseFailAlloc_7108_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                leanh::lean_ctor_set_uint8(
                    v___x_7107_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2 + 1) as u32,
                    v___y_7105_,
                );
                v_a_6982_ = v___x_7107_;
                v_e_x27_6983_ = v_e_x27_7095_;
                state = 2;
                continue;
            }
            24 => {
                if v_isShared_7112_ == 0 {
                    v___x_7114_ = v___x_7111_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7115_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7115_, 0, v_a_7109_);
                    v___x_7114_ = v_reuseFailAlloc_7115_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7114_;
            }
            26 => {
                return v___x_7121_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_tryMatcher___boxed(
    mut v_e_7127_: *mut leanh::LeanObject,
    mut v_a_7128_: *mut leanh::LeanObject,
    mut v_a_7129_: *mut leanh::LeanObject,
    mut v_a_7130_: *mut leanh::LeanObject,
    mut v_a_7131_: *mut leanh::LeanObject,
    mut v_a_7132_: *mut leanh::LeanObject,
    mut v_a_7133_: *mut leanh::LeanObject,
    mut v_a_7134_: *mut leanh::LeanObject,
    mut v_a_7135_: *mut leanh::LeanObject,
    mut v_a_7136_: *mut leanh::LeanObject,
    mut v_a_7137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7138_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(
        v_e_7127_, v_a_7128_, v_a_7129_, v_a_7130_, v_a_7131_, v_a_7132_, v_a_7133_, v_a_7134_,
        v_a_7135_, v_a_7136_,
    );
    leanh::lean_dec(v_a_7136_);
    leanh::lean_dec_ref(v_a_7135_);
    leanh::lean_dec(v_a_7134_);
    leanh::lean_dec_ref(v_a_7133_);
    leanh::lean_dec(v_a_7132_);
    leanh::lean_dec_ref(v_a_7131_);
    leanh::lean_dec(v_a_7130_);
    leanh::lean_dec_ref(v_a_7129_);
    leanh::lean_dec(v_a_7128_);
    return v_res_7138_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Sym_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__24_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_16_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2706181572____hygCtx___hyg_18_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__41_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_16_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDIteCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_2504619247____hygCtx___hyg_18_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__58_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_13_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Sym_Simp_simpDecideCbv_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_712439819____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__69_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_15_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpCbvCond_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_1028153571____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0____regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__77_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_17_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec___regBuiltin___private_Lean_Meta_Tactic_Cbv_ControlFlow_0__Lean_Meta_Tactic_Cbv_simpDecidableRec_declare__1_00___x40_Lean_Meta_Tactic_Cbv_ControlFlow_3691884447____hygCtx___hyg_19_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_ControlFlow(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Rewrite(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_ControlFlow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InferType(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Sym_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_NoncomputableAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
}