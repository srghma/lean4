// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: Init.Grind.Propagator Init.Simproc Init.Grind.Norm Lean.Meta.Tactic.Grind.Internalize Lean.Meta.Tactic.Grind.Anchor Lean.Meta.Tactic.Grind.EqResolution Lean.Meta.Tactic.Grind.SynthInstance Lean.Meta.Tactic.Grind.PropagatorAttr Init.Grind.Lemmas
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Grind::Lemmas::{
    initialize_Init_Grind_Lemmas, runtime_initialize_Init_Grind_Lemmas,
};
use crate::r#gen::Init::Grind::Norm::{
    initialize_Init_Grind_Norm, runtime_initialize_Init_Grind_Norm,
};
use crate::r#gen::Init::Grind::Propagator::{
    initialize_Init_Grind_Propagator, runtime_initialize_Init_Grind_Propagator,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_bvar___override, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_headBeta, l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf,
    l_Lean_mkAnd, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkConst,
    l_Lean_mkForall, l_Lean_mkLambda, l_Lean_mkNot, l_Lean_mkOr, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkOfEqFalseCore, l_Lean_Meta_mkOfEqTrueCore,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Anchor::{
    initialize_Lean_Meta_Tactic_Grind_Anchor, l_Lean_Meta_Grind_AnchorRef_matches,
    l_Lean_Meta_Grind_getAnchor, runtime_initialize_Lean_Meta_Tactic_Grind_Anchor,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EMatchTheorem::{
    l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns,
    l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::EqResolution::{
    initialize_Lean_Meta_Tactic_Grind_EqResolution, l_Lean_Meta_Grind_eqResolution,
    runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Internalize::{
    initialize_Lean_Meta_Tactic_Grind_Internalize, l_Lean_Meta_Grind_activateTheorem,
    runtime_initialize_Lean_Meta_Tactic_Grind_Internalize,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::PropagatorAttr::{
    initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
    l_Lean_Meta_Grind_registerBuiltinDownwardPropagator,
    runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_addNewRawFact, l_Lean_Meta_Grind_alreadyInternalized___redArg,
    l_Lean_Meta_Grind_getAnchorRefs___redArg, l_Lean_Meta_Grind_getGeneration___redArg,
    l_Lean_Meta_Grind_getSymbolPriorities___redArg, l_Lean_Meta_Grind_isEqFalse___redArg,
    l_Lean_Meta_Grind_isEqTrue___redArg, l_Lean_Meta_Grind_mkEqFalseProof,
    l_Lean_Meta_Grind_mkEqTrueProof, l_Lean_Meta_Grind_pushEqCore___redArg,
    l_Lean_Meta_Grind_pushEqFalse___redArg, l_Lean_Meta_Grind_pushEqTrue___redArg,
    l_Lean_Meta_Grind_updateLastTag,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    l_Lean_Meta_Simp_Simprocs_add, l_Lean_Meta_Simp_registerBuiltinSimproc,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_Result_getProof;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::{
    lean_expr_eqv, lean_expr_instantiate1, lean_expr_lift_loose_bvars,
};
use crate::ffi::lean_infer_type;
use crate::ffi::{
    lean_grind_internalize, lean_grind_preprocess,
};
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 105, 109, 112, 95, 101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2_value) as *mut crate::leanh::LeanObject,3900496790994782039 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 109, 112, 95, 101, 113, 95, 111, 102, 95, 101, 113, 95, 116, 114, 117, 101, 95, 114, 105, 103, 104, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5_value) as *mut crate::leanh::LeanObject,3307372134185396366 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [105, 109, 112, 95, 101, 113, 95, 111, 102, 95, 101, 113, 95, 116, 114, 117, 101, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8_value) as *mut crate::leanh::LeanObject,16900374347845262151 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 109, 112, 95, 101, 113, 95, 111, 102, 95, 101, 113, 95, 102, 97, 108, 115, 101, 95, 108, 101, 102, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11_value) as *mut crate::leanh::LeanObject,17922332017821563719 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        102, 111, 114, 97, 108, 108, 95, 112, 114, 111, 112, 97, 103, 97, 116, 111, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        10648830774388154971 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [100, 101, 98, 117, 103, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        102, 111, 114, 97, 108, 108, 80, 114, 111, 112, 97, 103, 97, 116, 111, 114, 0,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__4_value)
            as *mut crate::leanh::LeanObject,
        5637236024813792860 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__5_value)
            as *mut crate::leanh::LeanObject,
        9465863317062095934 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__8_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [113, 39, 58, 32, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__10_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 102, 111, 114, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropUp___closed__12_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [105, 115, 69, 113, 84, 114, 117, 101, 44, 32, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropUp___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__0_value) as *mut crate::leanh::LeanObject,5128563302434957432 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [101, 113, 95, 116, 114, 117, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__2_value) as *mut crate::leanh::LeanObject,12633671826946381106 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__4_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__5_value) as *mut crate::leanh::LeanObject,5647098122476602039 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0_value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 69, 45, 109, 97, 116, 99, 104, 32, 108, 111, 99, 97, 108, 32, 116, 104, 101, 111, 114, 101, 109, 32, 102, 111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 8 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 113, 82, 101, 115, 111, 108, 117, 116, 105, 111, 110, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropUp___closed__3_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__0_value)
            as *mut crate::leanh::LeanObject,
        14950941446142498629 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__3_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [44, 32, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [69, 120, 105, 115, 116, 115, 0],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__5_value)
            as *mut crate::leanh::LeanObject,
        5086165725197901121 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        111, 102, 95, 102, 111, 114, 97, 108, 108, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__7_value)
            as *mut crate::leanh::LeanObject,
        13897219834031082669 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 105, 109, 112, 95, 101, 113, 95, 102,
        97, 108, 115, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__9_value)
            as *mut crate::leanh::LeanObject,
        11068676920436378190 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 105, 109, 112, 95, 101, 113, 95,
        102, 97, 108, 115, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__12_value)
            as *mut crate::leanh::LeanObject,
        7271669433579898336 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateForallPropDown___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateExistsDown___closed__0_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 111, 116, 0],
};
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateExistsDown___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16612019923665488825 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateExistsDown___closed__4_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [120, 0],
};
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateExistsDown___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__4_value)
            as *mut crate::leanh::LeanObject,
        13655884332201764339 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateExistsDown___closed__6_value: crate::leanh::LeanStringObject<
    25,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        102, 111, 114, 97, 108, 108, 95, 110, 111, 116, 95, 111, 102, 95, 110, 111, 116, 95, 101,
        120, 105, 115, 116, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateExistsDown___closed__7_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__6_value)
            as *mut crate::leanh::LeanObject,
        1126875005015339072 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_propagateExistsDown___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateExistsDown___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0_value) as *mut crate::leanh::LeanObject,7839396180116328695 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2_value) as *mut crate::leanh::LeanObject,907667957179513571 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__1_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [79, 114, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__1_value)
                as *mut crate::leanh::LeanObject,
            14181099489592536354 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [65, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__3_value)
                as *mut crate::leanh::LeanObject,
            9743492140944907313 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__5_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [102, 111, 114, 97, 108, 108, 95, 97, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__6_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__5_value)
                as *mut crate::leanh::LeanObject,
            9297911139714337361 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__7_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            102, 111, 114, 97, 108, 108, 95, 102, 111, 114, 97, 108, 108, 95, 111, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__8_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__8_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__7_value)
                as *mut crate::leanh::LeanObject,
            9342489748056731765 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__9_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            102, 111, 114, 97, 108, 108, 95, 111, 114, 95, 102, 111, 114, 97, 108, 108, 0,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__10_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__10_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__9_value)
                as *mut crate::leanh::LeanObject,
            11153132344449437305 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__11_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__12_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__11_value)
                as *mut crate::leanh::LeanObject,
            11870096045526947150 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__14_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 109, 112, 95, 115, 101, 108, 102, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__15_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__15_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__14_value)
                as *mut crate::leanh::LeanObject,
            12630949715732095142 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__16_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__17_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            102, 111, 114, 97, 108, 108, 95, 105, 109, 112, 95, 101, 113, 95, 111, 114, 0,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__17_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__18_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__18_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__17_value)
                as *mut crate::leanh::LeanObject,
            6268712354196353085 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__19_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 109, 112, 95, 116, 114, 117, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__19_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__20_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__20_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__19_value)
                as *mut crate::leanh::LeanObject,
            3092345028705222935 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__22_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [105, 109, 112, 95, 102, 97, 108, 115, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__23_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__23_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__22_value)
                as *mut crate::leanh::LeanObject,
            4683752173772627417 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__25_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [116, 114, 117, 101, 95, 105, 109, 112, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__25_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__26_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__26_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__25_value)
                as *mut crate::leanh::LeanObject,
            11128255342867749396 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__26_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__28_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [102, 97, 108, 115, 101, 95, 105, 109, 112, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__28_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__29_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__29_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__28_value)
                as *mut crate::leanh::LeanObject,
            929721247191371647 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__29_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__30_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__31_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [105, 110, 116, 114, 111, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__31_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__11_value)
                as *mut crate::leanh::LeanObject,
            11870096045526947150 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpForall___closed__32_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__32_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__31_value)
                as *mut crate::leanh::LeanObject,
            18067798339771668657 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__32_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__33_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__34_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [102, 111, 114, 97, 108, 108, 95, 116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__34_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpForall___closed__35_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpForall___closed__35_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__35_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpForall___closed__35_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__35_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__34_value)
                as *mut crate::leanh::LeanObject,
            4727877053311152983 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__35_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__36_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpForall___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_simpForall___closed__38_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpForall___closed__39_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [102, 111, 114, 97, 108, 108, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpForall___closed__40_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__39_value)
                as *mut crate::leanh::LeanObject,
            9668247132177391628 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpForall___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpForall___closed__40_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpForall___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpForall___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 105, 109, 112, 70, 111, 114, 97, 108, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject,1564301828695695823 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value: crate::leanh::LeanArrayObject<2> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [((( 5 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__0_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [78, 111, 110, 101, 109, 112, 116, 121, 0],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13229434762204987278 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__2_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [101, 120, 105, 115, 116, 115, 95, 99, 111, 110, 115, 116, 0],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__3_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__3_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        5165052566337147184 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__4_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [101, 120, 105, 115, 116, 115, 95, 112, 114, 111, 112, 0],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
        51284145474571986 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__7_value: crate::leanh::LeanStringObject<
    17,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 17,
    m_capacity: 17,
    m_length: 16,
    m_data: [
        101, 120, 105, 115, 116, 115, 95, 97, 110, 100, 95, 114, 105, 103, 104, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__8_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__8_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__7_value)
            as *mut crate::leanh::LeanObject,
        17130565214221000006 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__9_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        101, 120, 105, 115, 116, 115, 95, 97, 110, 100, 95, 108, 101, 102, 116, 0,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__10_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__10_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__9_value)
            as *mut crate::leanh::LeanObject,
        4979233900843993299 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__11_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [101, 120, 105, 115, 116, 115, 95, 111, 114, 0],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Meta_Grind_simpExists___redArg___closed__12_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__12_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__11_value)
            as *mut crate::leanh::LeanObject,
        13373618201328513185 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_simpExists___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpExists___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 105, 109, 112, 69, 120, 105, 115, 116, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11__value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1_value) as *mut crate::leanh::LeanObject,15218882539576375456 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,16667980160077147100 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_propagateForallPropDown___closed__6_value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value: crate::leanh::LeanArrayObject<3> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10__value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2766_ = crate::leanh::lean_box(0);
    v___x_2767_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3;
    v___x_2768_ = l_Lean_mkConst(v___x_2767_, v___x_2766_);
    return v___x_2768_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2774_ = crate::leanh::lean_box(0);
    v___x_2775_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6;
    v___x_2776_ = l_Lean_mkConst(v___x_2775_, v___x_2774_);
    return v___x_2776_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2782_ = crate::leanh::lean_box(0);
    v___x_2783_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9;
    v___x_2784_ = l_Lean_mkConst(v___x_2783_, v___x_2782_);
    return v___x_2784_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2790_ = crate::leanh::lean_box(0);
    v___x_2791_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12;
    v___x_2792_ = l_Lean_mkConst(v___x_2791_, v___x_2790_);
    return v___x_2792_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(
    mut v_e_2793_: *mut crate::leanh::LeanObject,
    mut v_a_2794_: *mut crate::leanh::LeanObject,
    mut v_b_2795_: *mut crate::leanh::LeanObject,
    mut v_a_2796_: *mut crate::leanh::LeanObject,
    mut v_a_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: *mut crate::leanh::LeanObject,
    mut v_a_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
    mut v_a_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
    mut v_a_2805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2813_: u8 = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2832_: u8 = 0;
    let mut v_a_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_a_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v___y_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: u8 = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: u8 = 0;
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2869_: u8 = 0;
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2873_: u8 = 0;
    let mut v_a_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2877_: u8 = 0;
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2881_: u8 = 0;
    let mut v___y_2883_: u8 = 0;
    let mut v___y_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: u8 = 0;
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v_a_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2907_: u8 = 0;
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut v___y_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: u8 = 0;
    let mut v___x_2919_: u8 = 0;
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: u8 = 0;
    let mut v___x_2922_: u8 = 0;
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_a_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v___x_2949_: u8 = 0;
    let mut v___x_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: u8 = 0;
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut v_a_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2962_: u8 = 0;
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2944_ = l_Lean_Meta_Grind_alreadyInternalized___redArg(v_b_2795_, v_a_2796_);
                if crate::leanh::lean_obj_tag(v___x_2944_) == 0 {
                    v_a_2945_ = crate::leanh::lean_ctor_get(v___x_2944_, 0);
                    v_isSharedCheck_2958_ = (!crate::leanh::lean_is_exclusive(v___x_2944_)) as u8;
                    if v_isSharedCheck_2958_ == 0 {
                        v___x_2947_ = v___x_2944_;
                        v_isShared_2948_ = v_isSharedCheck_2958_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2945_);
                        crate::leanh::lean_dec(v___x_2944_);
                        v___x_2947_ = crate::leanh::lean_box(0);
                        v_isShared_2948_ = v_isSharedCheck_2958_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2795_);
                    crate::leanh::lean_dec_ref(v_a_2794_);
                    crate::leanh::lean_dec_ref(v_e_2793_);
                    v_a_2959_ = crate::leanh::lean_ctor_get(v___x_2944_, 0);
                    v_isSharedCheck_2966_ = (!crate::leanh::lean_is_exclusive(v___x_2944_)) as u8;
                    if v_isSharedCheck_2966_ == 0 {
                        v___x_2961_ = v___x_2944_;
                        v_isShared_2962_ = v_isSharedCheck_2966_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2959_);
                        crate::leanh::lean_dec(v___x_2944_);
                        v___x_2961_ = crate::leanh::lean_box(0);
                        v_isShared_2962_ = v_isSharedCheck_2966_;
                        state = 27;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2808_) == 0 {
                    v_a_2809_ = crate::leanh::lean_ctor_get(v___y_2808_, 0);
                    v_isSharedCheck_2841_ = (!crate::leanh::lean_is_exclusive(v___y_2808_)) as u8;
                    if v_isSharedCheck_2841_ == 0 {
                        v___x_2811_ = v___y_2808_;
                        v_isShared_2812_ = v_isSharedCheck_2841_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2809_);
                        crate::leanh::lean_dec(v___y_2808_);
                        v___x_2811_ = crate::leanh::lean_box(0);
                        v_isShared_2812_ = v_isSharedCheck_2841_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2795_);
                    crate::leanh::lean_dec_ref(v_a_2794_);
                    crate::leanh::lean_dec_ref(v_e_2793_);
                    v_a_2842_ = crate::leanh::lean_ctor_get(v___y_2808_, 0);
                    v_isSharedCheck_2849_ = (!crate::leanh::lean_is_exclusive(v___y_2808_)) as u8;
                    if v_isSharedCheck_2849_ == 0 {
                        v___x_2844_ = v___y_2808_;
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2842_);
                        crate::leanh::lean_dec(v___y_2808_);
                        v___x_2844_ = crate::leanh::lean_box(0);
                        v_isShared_2845_ = v_isSharedCheck_2849_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2813_ = (crate::leanh::lean_unbox(v_a_2809_) as u8);
                crate::leanh::lean_dec(v_a_2809_);
                if v___x_2813_ == 0 {
                    crate::leanh::lean_dec_ref(v_b_2795_);
                    crate::leanh::lean_dec_ref(v_a_2794_);
                    crate::leanh::lean_dec_ref(v_e_2793_);
                    v___x_2814_ = crate::leanh::lean_box(0);
                    if v_isShared_2812_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2811_, 0, v___x_2814_);
                        v___x_2816_ = v___x_2811_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2817_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2814_);
                        v___x_2816_ = v_reuseFailAlloc_2817_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2811_);
                    v___x_2818_ = l_Lean_Meta_Grind_mkEqTrueProof(
                        v_e_2793_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_,
                        v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2818_) == 0 {
                        v_a_2819_ = crate::leanh::lean_ctor_get(v___x_2818_, 0);
                        crate::leanh::lean_inc(v_a_2819_);
                        crate::leanh::lean_dec_ref_known(v___x_2818_, 1);
                        crate::leanh::lean_inc_ref(v_b_2795_);
                        v___x_2820_ = l_Lean_Meta_Grind_mkEqFalseProof(
                            v_b_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_,
                            v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2820_) == 0 {
                            v_a_2821_ = crate::leanh::lean_ctor_get(v___x_2820_, 0);
                            crate::leanh::lean_inc(v_a_2821_);
                            crate::leanh::lean_dec_ref_known(v___x_2820_, 1);
                            v___x_2822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
                            crate::leanh::lean_inc_ref(v_a_2794_);
                            v___x_2823_ = l_Lean_mkApp4(
                                v___x_2822_,
                                v_a_2794_,
                                v_b_2795_,
                                v_a_2819_,
                                v_a_2821_,
                            );
                            v___x_2824_ = l_Lean_Meta_Grind_pushEqFalse___redArg(
                                v_a_2794_,
                                v___x_2823_,
                                v_a_2796_,
                                v_a_2798_,
                                v_a_2800_,
                                v_a_2802_,
                                v_a_2803_,
                                v_a_2804_,
                                v_a_2805_,
                            );
                            return v___x_2824_;
                        } else {
                            crate::leanh::lean_dec(v_a_2819_);
                            crate::leanh::lean_dec_ref(v_b_2795_);
                            crate::leanh::lean_dec_ref(v_a_2794_);
                            v_a_2825_ = crate::leanh::lean_ctor_get(v___x_2820_, 0);
                            v_isSharedCheck_2832_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2820_)) as u8;
                            if v_isSharedCheck_2832_ == 0 {
                                v___x_2827_ = v___x_2820_;
                                v_isShared_2828_ = v_isSharedCheck_2832_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2825_);
                                crate::leanh::lean_dec(v___x_2820_);
                                v___x_2827_ = crate::leanh::lean_box(0);
                                v_isShared_2828_ = v_isSharedCheck_2832_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_2795_);
                        crate::leanh::lean_dec_ref(v_a_2794_);
                        v_a_2833_ = crate::leanh::lean_ctor_get(v___x_2818_, 0);
                        v_isSharedCheck_2840_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2818_)) as u8;
                        if v_isSharedCheck_2840_ == 0 {
                            v___x_2835_ = v___x_2818_;
                            v_isShared_2836_ = v_isSharedCheck_2840_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2833_);
                            crate::leanh::lean_dec(v___x_2818_);
                            v___x_2835_ = crate::leanh::lean_box(0);
                            v_isShared_2836_ = v_isSharedCheck_2840_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_2816_;
            }
            4 => {
                if v_isShared_2828_ == 0 {
                    v___x_2830_ = v___x_2827_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2831_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
                    v___x_2830_ = v_reuseFailAlloc_2831_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2830_;
            }
            6 => {
                if v_isShared_2836_ == 0 {
                    v___x_2838_ = v___x_2835_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2833_);
                    v___x_2838_ = v_reuseFailAlloc_2839_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2838_;
            }
            8 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2847_;
            }
            10 => {
                if crate::leanh::lean_obj_tag(v___y_2851_) == 0 {
                    v_a_2852_ = crate::leanh::lean_ctor_get(v___y_2851_, 0);
                    crate::leanh::lean_inc(v_a_2852_);
                    crate::leanh::lean_dec_ref_known(v___y_2851_, 1);
                    v___x_2853_ = (crate::leanh::lean_unbox(v_a_2852_) as u8);
                    crate::leanh::lean_dec(v_a_2852_);
                    if v___x_2853_ == 0 {
                        crate::leanh::lean_inc_ref(v_b_2795_);
                        v___x_2854_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                            v_b_2795_, v_a_2796_, v_a_2800_, v_a_2802_, v_a_2803_, v_a_2804_,
                            v_a_2805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2854_) == 0 {
                            v_a_2855_ = crate::leanh::lean_ctor_get(v___x_2854_, 0);
                            crate::leanh::lean_inc(v_a_2855_);
                            v___x_2856_ = (crate::leanh::lean_unbox(v_a_2855_) as u8);
                            crate::leanh::lean_dec(v_a_2855_);
                            if v___x_2856_ == 0 {
                                v___y_2808_ = v___x_2854_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2854_, 1);
                                crate::leanh::lean_inc_ref(v_e_2793_);
                                v___x_2857_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                                    v_e_2793_, v_a_2796_, v_a_2800_, v_a_2802_, v_a_2803_,
                                    v_a_2804_, v_a_2805_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2857_) == 0 {
                                    v_a_2858_ = crate::leanh::lean_ctor_get(v___x_2857_, 0);
                                    crate::leanh::lean_inc(v_a_2858_);
                                    v___x_2859_ = (crate::leanh::lean_unbox(v_a_2858_) as u8);
                                    crate::leanh::lean_dec(v_a_2858_);
                                    if v___x_2859_ == 0 {
                                        v___y_2808_ = v___x_2857_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_2857_, 1);
                                        crate::leanh::lean_inc_ref(v_a_2794_);
                                        v___x_2860_ = l_Lean_Meta_isProp(
                                            v_a_2794_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                                        );
                                        v___y_2808_ = v___x_2860_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_2808_ = v___x_2857_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___y_2808_ = v___x_2854_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_b_2795_);
                        v___x_2861_ = l_Lean_Meta_Grind_mkEqTrueProof(
                            v_b_2795_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_,
                            v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2861_) == 0 {
                            v_a_2862_ = crate::leanh::lean_ctor_get(v___x_2861_, 0);
                            crate::leanh::lean_inc(v_a_2862_);
                            crate::leanh::lean_dec_ref_known(v___x_2861_, 1);
                            v___x_2863_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7);
                            v___x_2864_ =
                                l_Lean_mkApp3(v___x_2863_, v_a_2794_, v_b_2795_, v_a_2862_);
                            v___x_2865_ = l_Lean_Meta_Grind_pushEqTrue___redArg(
                                v_e_2793_,
                                v___x_2864_,
                                v_a_2796_,
                                v_a_2798_,
                                v_a_2800_,
                                v_a_2802_,
                                v_a_2803_,
                                v_a_2804_,
                                v_a_2805_,
                            );
                            return v___x_2865_;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2795_);
                            crate::leanh::lean_dec_ref(v_a_2794_);
                            crate::leanh::lean_dec_ref(v_e_2793_);
                            v_a_2866_ = crate::leanh::lean_ctor_get(v___x_2861_, 0);
                            v_isSharedCheck_2873_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2861_)) as u8;
                            if v_isSharedCheck_2873_ == 0 {
                                v___x_2868_ = v___x_2861_;
                                v_isShared_2869_ = v_isSharedCheck_2873_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2866_);
                                crate::leanh::lean_dec(v___x_2861_);
                                v___x_2868_ = crate::leanh::lean_box(0);
                                v_isShared_2869_ = v_isSharedCheck_2873_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2795_);
                    crate::leanh::lean_dec_ref(v_a_2794_);
                    crate::leanh::lean_dec_ref(v_e_2793_);
                    v_a_2874_ = crate::leanh::lean_ctor_get(v___y_2851_, 0);
                    v_isSharedCheck_2881_ = (!crate::leanh::lean_is_exclusive(v___y_2851_)) as u8;
                    if v_isSharedCheck_2881_ == 0 {
                        v___x_2876_ = v___y_2851_;
                        v_isShared_2877_ = v_isSharedCheck_2881_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2874_);
                        crate::leanh::lean_dec(v___y_2851_);
                        v___x_2876_ = crate::leanh::lean_box(0);
                        v_isShared_2877_ = v_isSharedCheck_2881_;
                        state = 13;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_2869_ == 0 {
                    v___x_2871_ = v___x_2868_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
                    v___x_2871_ = v_reuseFailAlloc_2872_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2871_;
            }
            13 => {
                if v_isShared_2877_ == 0 {
                    v___x_2879_ = v___x_2876_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
                    v___x_2879_ = v_reuseFailAlloc_2880_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2879_;
            }
            15 => {
                if crate::leanh::lean_obj_tag(v___y_2884_) == 0 {
                    v_a_2885_ = crate::leanh::lean_ctor_get(v___y_2884_, 0);
                    crate::leanh::lean_inc(v_a_2885_);
                    crate::leanh::lean_dec_ref_known(v___y_2884_, 1);
                    v___x_2886_ = (crate::leanh::lean_unbox(v_a_2885_) as u8);
                    crate::leanh::lean_dec(v_a_2885_);
                    if v___x_2886_ == 0 {
                        crate::leanh::lean_inc_ref(v_b_2795_);
                        v___x_2887_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                            v_b_2795_, v_a_2796_, v_a_2800_, v_a_2802_, v_a_2803_, v_a_2804_,
                            v_a_2805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2887_) == 0 {
                            v_a_2888_ = crate::leanh::lean_ctor_get(v___x_2887_, 0);
                            crate::leanh::lean_inc(v_a_2888_);
                            v___x_2889_ = (crate::leanh::lean_unbox(v_a_2888_) as u8);
                            crate::leanh::lean_dec(v_a_2888_);
                            if v___x_2889_ == 0 {
                                v___y_2851_ = v___x_2887_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2887_, 1);
                                crate::leanh::lean_inc_ref(v_a_2794_);
                                v___x_2890_ = l_Lean_Meta_isProp(
                                    v_a_2794_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                                );
                                v___y_2851_ = v___x_2890_;
                                state = 10;
                                continue;
                            }
                        } else {
                            v___y_2851_ = v___x_2887_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_a_2794_);
                        v___x_2891_ = l_Lean_Meta_Grind_mkEqTrueProof(
                            v_a_2794_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_,
                            v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2891_) == 0 {
                            v_a_2892_ = crate::leanh::lean_ctor_get(v___x_2891_, 0);
                            crate::leanh::lean_inc(v_a_2892_);
                            crate::leanh::lean_dec_ref_known(v___x_2891_, 1);
                            v___x_2893_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10);
                            crate::leanh::lean_inc_ref(v_b_2795_);
                            v___x_2894_ =
                                l_Lean_mkApp3(v___x_2893_, v_a_2794_, v_b_2795_, v_a_2892_);
                            v___x_2895_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                                v_e_2793_,
                                v_b_2795_,
                                v___x_2894_,
                                v___y_2883_,
                                v_a_2796_,
                                v_a_2798_,
                                v_a_2802_,
                                v_a_2803_,
                                v_a_2804_,
                                v_a_2805_,
                            );
                            return v___x_2895_;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2795_);
                            crate::leanh::lean_dec_ref(v_a_2794_);
                            crate::leanh::lean_dec_ref(v_e_2793_);
                            v_a_2896_ = crate::leanh::lean_ctor_get(v___x_2891_, 0);
                            v_isSharedCheck_2903_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2891_)) as u8;
                            if v_isSharedCheck_2903_ == 0 {
                                v___x_2898_ = v___x_2891_;
                                v_isShared_2899_ = v_isSharedCheck_2903_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2896_);
                                crate::leanh::lean_dec(v___x_2891_);
                                v___x_2898_ = crate::leanh::lean_box(0);
                                v_isShared_2899_ = v_isSharedCheck_2903_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2795_);
                    crate::leanh::lean_dec_ref(v_a_2794_);
                    crate::leanh::lean_dec_ref(v_e_2793_);
                    v_a_2904_ = crate::leanh::lean_ctor_get(v___y_2884_, 0);
                    v_isSharedCheck_2911_ = (!crate::leanh::lean_is_exclusive(v___y_2884_)) as u8;
                    if v_isSharedCheck_2911_ == 0 {
                        v___x_2906_ = v___y_2884_;
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2904_);
                        crate::leanh::lean_dec(v___y_2884_);
                        v___x_2906_ = crate::leanh::lean_box(0);
                        v_isShared_2907_ = v_isSharedCheck_2911_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_2899_ == 0 {
                    v___x_2901_ = v___x_2898_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
                    v___x_2901_ = v_reuseFailAlloc_2902_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2901_;
            }
            18 => {
                if v_isShared_2907_ == 0 {
                    v___x_2909_ = v___x_2906_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
                    v___x_2909_ = v_reuseFailAlloc_2910_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2909_;
            }
            20 => {
                if crate::leanh::lean_obj_tag(v___y_2913_) == 0 {
                    v_a_2914_ = crate::leanh::lean_ctor_get(v___y_2913_, 0);
                    crate::leanh::lean_inc(v_a_2914_);
                    crate::leanh::lean_dec_ref_known(v___y_2913_, 1);
                    v___x_2915_ = (crate::leanh::lean_unbox(v_a_2914_) as u8);
                    if v___x_2915_ == 0 {
                        crate::leanh::lean_inc_ref(v_a_2794_);
                        v___x_2916_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                            v_a_2794_, v_a_2796_, v_a_2800_, v_a_2802_, v_a_2803_, v_a_2804_,
                            v_a_2805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2916_) == 0 {
                            v_a_2917_ = crate::leanh::lean_ctor_get(v___x_2916_, 0);
                            crate::leanh::lean_inc(v_a_2917_);
                            v___x_2918_ = (crate::leanh::lean_unbox(v_a_2917_) as u8);
                            crate::leanh::lean_dec(v_a_2917_);
                            if v___x_2918_ == 0 {
                                v___x_2919_ = (crate::leanh::lean_unbox(v_a_2914_) as u8);
                                crate::leanh::lean_dec(v_a_2914_);
                                v___y_2883_ = v___x_2919_;
                                v___y_2884_ = v___x_2916_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_2916_, 1);
                                crate::leanh::lean_inc_ref(v_b_2795_);
                                v___x_2920_ = l_Lean_Meta_isProp(
                                    v_b_2795_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                                );
                                v___x_2921_ = (crate::leanh::lean_unbox(v_a_2914_) as u8);
                                crate::leanh::lean_dec(v_a_2914_);
                                v___y_2883_ = v___x_2921_;
                                v___y_2884_ = v___x_2920_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v___x_2922_ = (crate::leanh::lean_unbox(v_a_2914_) as u8);
                            crate::leanh::lean_dec(v_a_2914_);
                            v___y_2883_ = v___x_2922_;
                            v___y_2884_ = v___x_2916_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2914_);
                        crate::leanh::lean_inc_ref(v_a_2794_);
                        v___x_2923_ = l_Lean_Meta_Grind_mkEqFalseProof(
                            v_a_2794_, v_a_2796_, v_a_2797_, v_a_2798_, v_a_2799_, v_a_2800_,
                            v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2923_) == 0 {
                            v_a_2924_ = crate::leanh::lean_ctor_get(v___x_2923_, 0);
                            crate::leanh::lean_inc(v_a_2924_);
                            crate::leanh::lean_dec_ref_known(v___x_2923_, 1);
                            v___x_2925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13_once), _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13);
                            v___x_2926_ =
                                l_Lean_mkApp3(v___x_2925_, v_a_2794_, v_b_2795_, v_a_2924_);
                            v___x_2927_ = l_Lean_Meta_Grind_pushEqTrue___redArg(
                                v_e_2793_,
                                v___x_2926_,
                                v_a_2796_,
                                v_a_2798_,
                                v_a_2800_,
                                v_a_2802_,
                                v_a_2803_,
                                v_a_2804_,
                                v_a_2805_,
                            );
                            return v___x_2927_;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_2795_);
                            crate::leanh::lean_dec_ref(v_a_2794_);
                            crate::leanh::lean_dec_ref(v_e_2793_);
                            v_a_2928_ = crate::leanh::lean_ctor_get(v___x_2923_, 0);
                            v_isSharedCheck_2935_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2923_)) as u8;
                            if v_isSharedCheck_2935_ == 0 {
                                v___x_2930_ = v___x_2923_;
                                v_isShared_2931_ = v_isSharedCheck_2935_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2928_);
                                crate::leanh::lean_dec(v___x_2923_);
                                v___x_2930_ = crate::leanh::lean_box(0);
                                v_isShared_2931_ = v_isSharedCheck_2935_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_b_2795_);
                    crate::leanh::lean_dec_ref(v_a_2794_);
                    crate::leanh::lean_dec_ref(v_e_2793_);
                    v_a_2936_ = crate::leanh::lean_ctor_get(v___y_2913_, 0);
                    v_isSharedCheck_2943_ = (!crate::leanh::lean_is_exclusive(v___y_2913_)) as u8;
                    if v_isSharedCheck_2943_ == 0 {
                        v___x_2938_ = v___y_2913_;
                        v_isShared_2939_ = v_isSharedCheck_2943_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2936_);
                        crate::leanh::lean_dec(v___y_2913_);
                        v___x_2938_ = crate::leanh::lean_box(0);
                        v_isShared_2939_ = v_isSharedCheck_2943_;
                        state = 23;
                        continue;
                    }
                }
            }
            21 => {
                if v_isShared_2931_ == 0 {
                    v___x_2933_ = v___x_2930_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2933_;
            }
            23 => {
                if v_isShared_2939_ == 0 {
                    v___x_2941_ = v___x_2938_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2941_;
            }
            25 => {
                v___x_2949_ = (crate::leanh::lean_unbox(v_a_2945_) as u8);
                crate::leanh::lean_dec(v_a_2945_);
                if v___x_2949_ == 0 {
                    crate::leanh::lean_dec_ref(v_b_2795_);
                    crate::leanh::lean_dec_ref(v_a_2794_);
                    crate::leanh::lean_dec_ref(v_e_2793_);
                    v___x_2950_ = crate::leanh::lean_box(0);
                    if v_isShared_2948_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2947_, 0, v___x_2950_);
                        v___x_2952_ = v___x_2947_;
                        state = 26;
                        continue;
                    } else {
                        v_reuseFailAlloc_2953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
                        v___x_2952_ = v_reuseFailAlloc_2953_;
                        state = 26;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2947_);
                    crate::leanh::lean_inc_ref(v_a_2794_);
                    v___x_2954_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                        v_a_2794_, v_a_2796_, v_a_2800_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2954_) == 0 {
                        v_a_2955_ = crate::leanh::lean_ctor_get(v___x_2954_, 0);
                        crate::leanh::lean_inc(v_a_2955_);
                        v___x_2956_ = (crate::leanh::lean_unbox(v_a_2955_) as u8);
                        crate::leanh::lean_dec(v_a_2955_);
                        if v___x_2956_ == 0 {
                            v___y_2913_ = v___x_2954_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2954_, 1);
                            crate::leanh::lean_inc_ref(v_b_2795_);
                            v___x_2957_ = l_Lean_Meta_isProp(
                                v_b_2795_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_,
                            );
                            v___y_2913_ = v___x_2957_;
                            state = 20;
                            continue;
                        }
                    } else {
                        v___y_2913_ = v___x_2954_;
                        state = 20;
                        continue;
                    }
                }
            }
            26 => {
                return v___x_2952_;
            }
            27 => {
                if v_isShared_2962_ == 0 {
                    v___x_2964_ = v___x_2961_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2965_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
                    v___x_2964_ = v_reuseFailAlloc_2965_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(
    mut v_e_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
    mut v_b_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
    mut v_a_2977_: *mut crate::leanh::LeanObject,
    mut v_a_2978_: *mut crate::leanh::LeanObject,
    mut v_a_2979_: *mut crate::leanh::LeanObject,
    mut v_a_2980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2981_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_2967_, v_a_2968_, v_b_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
    crate::leanh::lean_dec(v_a_2979_);
    crate::leanh::lean_dec_ref(v_a_2978_);
    crate::leanh::lean_dec(v_a_2977_);
    crate::leanh::lean_dec_ref(v_a_2976_);
    crate::leanh::lean_dec(v_a_2975_);
    crate::leanh::lean_dec_ref(v_a_2974_);
    crate::leanh::lean_dec(v_a_2973_);
    crate::leanh::lean_dec_ref(v_a_2972_);
    crate::leanh::lean_dec(v_a_2971_);
    crate::leanh::lean_dec(v_a_2970_);
    return v_res_2981_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateForallPropUp___lam__0(
    mut v_cls_2985_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
    mut v___y_2988_: *mut crate::leanh::LeanObject,
    mut v___y_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2999_: u8 = 0;
    v_options_2998_ = crate::leanh::lean_ctor_get(v___y_2995_, 2);
    v_hasTrace_2999_ = crate::leanh::lean_ctor_get_uint8(
        v_options_2998_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_2999_ == 0 {
        let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_cls_2985_);
        v___x_3000_ = crate::leanh::lean_box((v_hasTrace_2999_) as usize);
        v___x_3001_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3001_, 0, v___x_3000_);
        return v___x_3001_;
    } else {
        let mut v___x_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3004_: u8 = 0;
        let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3002_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1;
        v___x_3003_ = l_Lean_Name_append(v___x_3002_, v_cls_2985_);
        v___x_3004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_____do__lift_2986_,
            v_options_2998_,
            v___x_3003_,
        );
        crate::leanh::lean_dec(v___x_3003_);
        v___x_3005_ = crate::leanh::lean_box((v___x_3004_) as usize);
        v___x_3006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3006_, 0, v___x_3005_);
        return v___x_3006_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateForallPropUp___lam__0___boxed(
    mut v_cls_3007_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
    mut v___y_3015_: *mut crate::leanh::LeanObject,
    mut v___y_3016_: *mut crate::leanh::LeanObject,
    mut v___y_3017_: *mut crate::leanh::LeanObject,
    mut v___y_3018_: *mut crate::leanh::LeanObject,
    mut v___y_3019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3020_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(
        v_cls_3007_,
        v_____do__lift_3008_,
        v___y_3009_,
        v___y_3010_,
        v___y_3011_,
        v___y_3012_,
        v___y_3013_,
        v___y_3014_,
        v___y_3015_,
        v___y_3016_,
        v___y_3017_,
        v___y_3018_,
    );
    crate::leanh::lean_dec(v___y_3018_);
    crate::leanh::lean_dec_ref(v___y_3017_);
    crate::leanh::lean_dec(v___y_3016_);
    crate::leanh::lean_dec_ref(v___y_3015_);
    crate::leanh::lean_dec(v___y_3014_);
    crate::leanh::lean_dec_ref(v___y_3013_);
    crate::leanh::lean_dec(v___y_3012_);
    crate::leanh::lean_dec_ref(v___y_3011_);
    crate::leanh::lean_dec(v___y_3010_);
    crate::leanh::lean_dec(v___y_3009_);
    crate::leanh::lean_dec_ref(v_____do__lift_3008_);
    return v_res_3020_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(
    mut v_msgData_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = lean_st_ref_get(v___y_3025_);
    v_env_3028_ = crate::leanh::lean_ctor_get(v___x_3027_, 0);
    crate::leanh::lean_inc_ref(v_env_3028_);
    crate::leanh::lean_dec(v___x_3027_);
    v___x_3029_ = lean_st_ref_get(v___y_3023_);
    v_mctx_3030_ = crate::leanh::lean_ctor_get(v___x_3029_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3030_);
    crate::leanh::lean_dec(v___x_3029_);
    v_lctx_3031_ = crate::leanh::lean_ctor_get(v___y_3022_, 2);
    v_options_3032_ = crate::leanh::lean_ctor_get(v___y_3024_, 2);
    crate::leanh::lean_inc_ref(v_options_3032_);
    crate::leanh::lean_inc_ref(v_lctx_3031_);
    v___x_3033_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3033_, 0, v_env_3028_);
    crate::leanh::lean_ctor_set(v___x_3033_, 1, v_mctx_3030_);
    crate::leanh::lean_ctor_set(v___x_3033_, 2, v_lctx_3031_);
    crate::leanh::lean_ctor_set(v___x_3033_, 3, v_options_3032_);
    v___x_3034_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3034_, 0, v___x_3033_);
    crate::leanh::lean_ctor_set(v___x_3034_, 1, v_msgData_3021_);
    v___x_3035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3035_, 0, v___x_3034_);
    return v___x_3035_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0___boxed(
    mut v_msgData_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
    mut v___y_3038_: *mut crate::leanh::LeanObject,
    mut v___y_3039_: *mut crate::leanh::LeanObject,
    mut v___y_3040_: *mut crate::leanh::LeanObject,
    mut v___y_3041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3042_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msgData_3036_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
    crate::leanh::lean_dec(v___y_3040_);
    crate::leanh::lean_dec_ref(v___y_3039_);
    crate::leanh::lean_dec(v___y_3038_);
    crate::leanh::lean_dec_ref(v___y_3037_);
    return v_res_3042_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: f64 = 0.0;
    v___x_3043_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3044_ = lean_float_of_nat(v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(
    mut v_cls_3048_: *mut crate::leanh::LeanObject,
    mut v_msg_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3060_: u8 = 0;
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v_tid_3074_: u64 = 0;
    let mut v_traces_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3078_: u8 = 0;
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: f64 = 0.0;
    let mut v___x_3081_: u8 = 0;
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3099_: u8 = 0;
    let mut v_isSharedCheck_3100_: u8 = 0;
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3055_ = crate::leanh::lean_ctor_get(v___y_3052_, 5);
                v___x_3056_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0_spec__0(v_msg_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
                v_a_3057_ = crate::leanh::lean_ctor_get(v___x_3056_, 0);
                v_isSharedCheck_3101_ = (!crate::leanh::lean_is_exclusive(v___x_3056_)) as u8;
                if v_isSharedCheck_3101_ == 0 {
                    v___x_3059_ = v___x_3056_;
                    v_isShared_3060_ = v_isSharedCheck_3101_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3057_);
                    crate::leanh::lean_dec(v___x_3056_);
                    v___x_3059_ = crate::leanh::lean_box(0);
                    v_isShared_3060_ = v_isSharedCheck_3101_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3061_ = lean_st_ref_take(v___y_3053_);
                v_traceState_3062_ = crate::leanh::lean_ctor_get(v___x_3061_, 4);
                v_env_3063_ = crate::leanh::lean_ctor_get(v___x_3061_, 0);
                v_nextMacroScope_3064_ = crate::leanh::lean_ctor_get(v___x_3061_, 1);
                v_ngen_3065_ = crate::leanh::lean_ctor_get(v___x_3061_, 2);
                v_auxDeclNGen_3066_ = crate::leanh::lean_ctor_get(v___x_3061_, 3);
                v_cache_3067_ = crate::leanh::lean_ctor_get(v___x_3061_, 5);
                v_messages_3068_ = crate::leanh::lean_ctor_get(v___x_3061_, 6);
                v_infoState_3069_ = crate::leanh::lean_ctor_get(v___x_3061_, 7);
                v_snapshotTasks_3070_ = crate::leanh::lean_ctor_get(v___x_3061_, 8);
                v_isSharedCheck_3100_ = (!crate::leanh::lean_is_exclusive(v___x_3061_)) as u8;
                if v_isSharedCheck_3100_ == 0 {
                    v___x_3072_ = v___x_3061_;
                    v_isShared_3073_ = v_isSharedCheck_3100_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3070_);
                    crate::leanh::lean_inc(v_infoState_3069_);
                    crate::leanh::lean_inc(v_messages_3068_);
                    crate::leanh::lean_inc(v_cache_3067_);
                    crate::leanh::lean_inc(v_traceState_3062_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3066_);
                    crate::leanh::lean_inc(v_ngen_3065_);
                    crate::leanh::lean_inc(v_nextMacroScope_3064_);
                    crate::leanh::lean_inc(v_env_3063_);
                    crate::leanh::lean_dec(v___x_3061_);
                    v___x_3072_ = crate::leanh::lean_box(0);
                    v_isShared_3073_ = v_isSharedCheck_3100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3074_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3062_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3075_ = crate::leanh::lean_ctor_get(v_traceState_3062_, 0);
                v_isSharedCheck_3099_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3062_)) as u8;
                if v_isSharedCheck_3099_ == 0 {
                    v___x_3077_ = v_traceState_3062_;
                    v_isShared_3078_ = v_isSharedCheck_3099_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3075_);
                    crate::leanh::lean_dec(v_traceState_3062_);
                    v___x_3077_ = crate::leanh::lean_box(0);
                    v_isShared_3078_ = v_isSharedCheck_3099_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3079_ = crate::leanh::lean_box(0);
                v___x_3080_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0);
                v___x_3081_ = 0;
                v___x_3082_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1;
                v___x_3083_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3083_, 0, v_cls_3048_);
                crate::leanh::lean_ctor_set(v___x_3083_, 1, v___x_3079_);
                crate::leanh::lean_ctor_set(v___x_3083_, 2, v___x_3082_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3083_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3080_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3083_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3080_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3083_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3081_,
                );
                v___x_3084_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__2;
                v___x_3085_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3085_, 0, v___x_3083_);
                crate::leanh::lean_ctor_set(v___x_3085_, 1, v_a_3057_);
                crate::leanh::lean_ctor_set(v___x_3085_, 2, v___x_3084_);
                crate::leanh::lean_inc(v_ref_3055_);
                v___x_3086_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3086_, 0, v_ref_3055_);
                crate::leanh::lean_ctor_set(v___x_3086_, 1, v___x_3085_);
                v___x_3087_ = l_Lean_PersistentArray_push___redArg(v_traces_3075_, v___x_3086_);
                if v_isShared_3078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3077_, 0, v___x_3087_);
                    v___x_3089_ = v___x_3077_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3098_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3098_, 0, v___x_3087_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3098_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3074_,
                    );
                    v___x_3089_ = v_reuseFailAlloc_3098_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3072_, 4, v___x_3089_);
                    v___x_3091_ = v___x_3072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3097_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_env_3063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 1, v_nextMacroScope_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 2, v_ngen_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 3, v_auxDeclNGen_3066_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 4, v___x_3089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 5, v_cache_3067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 6, v_messages_3068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 7, v_infoState_3069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3097_, 8, v_snapshotTasks_3070_);
                    v___x_3091_ = v_reuseFailAlloc_3097_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3092_ = lean_st_ref_set(v___y_3053_, v___x_3091_);
                v___x_3093_ = crate::leanh::lean_box(0);
                if v_isShared_3060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3059_, 0, v___x_3093_);
                    v___x_3095_ = v___x_3059_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3096_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
                    v___x_3095_ = v_reuseFailAlloc_3096_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(
    mut v_cls_3102_: *mut crate::leanh::LeanObject,
    mut v_msg_3103_: *mut crate::leanh::LeanObject,
    mut v___y_3104_: *mut crate::leanh::LeanObject,
    mut v___y_3105_: *mut crate::leanh::LeanObject,
    mut v___y_3106_: *mut crate::leanh::LeanObject,
    mut v___y_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3109_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(
        v_cls_3102_,
        v_msg_3103_,
        v___y_3104_,
        v___y_3105_,
        v___y_3106_,
        v___y_3107_,
    );
    crate::leanh::lean_dec(v___y_3107_);
    crate::leanh::lean_dec_ref(v___y_3106_);
    crate::leanh::lean_dec(v___y_3105_);
    crate::leanh::lean_dec_ref(v___y_3104_);
    return v_res_3109_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3115_ = crate::leanh::lean_box(0);
    v___x_3116_ = l_Lean_Meta_Grind_propagateForallPropUp___closed__1;
    v___x_3117_ = l_Lean_mkConst(v___x_3116_, v___x_3115_);
    return v___x_3117_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_3125_ = l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
    v___x_3126_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1;
    v___x_3127_ = l_Lean_Name_append(v___x_3126_, v_cls_3125_);
    return v___x_3127_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
    v___x_3130_ = l_Lean_stringToMessageData(v___x_3129_);
    return v___x_3130_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3132_ = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
    v___x_3133_ = l_Lean_stringToMessageData(v___x_3132_);
    return v___x_3133_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3135_ = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
    v___x_3136_ = l_Lean_stringToMessageData(v___x_3135_);
    return v___x_3136_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateForallPropUp(
    mut v_e_3137_: *mut crate::leanh::LeanObject,
    mut v_a_3138_: *mut crate::leanh::LeanObject,
    mut v_a_3139_: *mut crate::leanh::LeanObject,
    mut v_a_3140_: *mut crate::leanh::LeanObject,
    mut v_a_3141_: *mut crate::leanh::LeanObject,
    mut v_a_3142_: *mut crate::leanh::LeanObject,
    mut v_a_3143_: *mut crate::leanh::LeanObject,
    mut v_a_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3152_: u8 = 0;
    let mut v___y_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: u8 = 0;
    let mut v___y_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3173_: u8 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3177_: u8 = 0;
    let mut v_inheritedTraceOptions_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3181_: u8 = 0;
    let mut v___y_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3205_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: u8 = 0;
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut v_a_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3233_: u8 = 0;
    let mut v_a_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3237_: u8 = 0;
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3241_: u8 = 0;
    let mut v___y_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: u8 = 0;
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3275_: u8 = 0;
    let mut v_a_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3279_: u8 = 0;
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3283_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_3137_) == 7 {
                    v_binderName_3149_ = crate::leanh::lean_ctor_get(v_e_3137_, 0);
                    v_binderType_3150_ = crate::leanh::lean_ctor_get(v_e_3137_, 1);
                    v_body_3151_ = crate::leanh::lean_ctor_get(v_e_3137_, 2);
                    v_binderInfo_3152_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_3137_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    v_inheritedTraceOptions_3178_ = crate::leanh::lean_ctor_get(v_a_3146_, 13);
                    v_cls_3179_ = l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
                    v___x_3284_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(
                        v_cls_3179_,
                        v_inheritedTraceOptions_3178_,
                        v_a_3138_,
                        v_a_3139_,
                        v_a_3140_,
                        v_a_3141_,
                        v_a_3142_,
                        v_a_3143_,
                        v_a_3144_,
                        v_a_3145_,
                        v_a_3146_,
                        v_a_3147_,
                    );
                    v_a_3285_ = crate::leanh::lean_ctor_get(v___x_3284_, 0);
                    crate::leanh::lean_inc(v_a_3285_);
                    crate::leanh::lean_dec_ref(v___x_3284_);
                    v___x_3286_ = (crate::leanh::lean_unbox(v_a_3285_) as u8);
                    crate::leanh::lean_dec(v_a_3285_);
                    if v___x_3286_ == 0 {
                        v___y_3243_ = v_a_3138_;
                        v___y_3244_ = v_a_3139_;
                        v___y_3245_ = v_a_3140_;
                        v___y_3246_ = v_a_3141_;
                        v___y_3247_ = v_a_3142_;
                        v___y_3248_ = v_a_3143_;
                        v___y_3249_ = v_a_3144_;
                        v___y_3250_ = v_a_3145_;
                        v___y_3251_ = v_a_3146_;
                        v___y_3252_ = v_a_3147_;
                        state = 11;
                        continue;
                    } else {
                        v___x_3287_ = l_Lean_Meta_Grind_updateLastTag(
                            v_a_3138_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_, v_a_3143_,
                            v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3287_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3287_, 1);
                            crate::leanh::lean_inc_ref(v_e_3137_);
                            v___x_3288_ = l_Lean_MessageData_ofExpr(v_e_3137_);
                            v___x_3289_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_3179_, v___x_3288_, v_a_3144_, v_a_3145_, v_a_3146_, v_a_3147_);
                            if crate::leanh::lean_obj_tag(v___x_3289_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3289_, 1);
                                v___y_3243_ = v_a_3138_;
                                v___y_3244_ = v_a_3139_;
                                v___y_3245_ = v_a_3140_;
                                v___y_3246_ = v_a_3141_;
                                v___y_3247_ = v_a_3142_;
                                v___y_3248_ = v_a_3143_;
                                v___y_3249_ = v_a_3144_;
                                v___y_3250_ = v_a_3145_;
                                v___y_3251_ = v_a_3146_;
                                v___y_3252_ = v_a_3147_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                                return v___x_3289_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                            return v___x_3287_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3137_);
                    v___x_3290_ = crate::leanh::lean_box(0);
                    v___x_3291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3291_, 0, v___x_3290_);
                    return v___x_3291_;
                }
            }
            1 => {
                v___x_3165_ = l_Lean_Meta_Simp_Result_getProof(
                    v___y_3154_,
                    v___y_3161_,
                    v___y_3162_,
                    v___y_3163_,
                    v___y_3164_,
                );
                if crate::leanh::lean_obj_tag(v___x_3165_) == 0 {
                    v_a_3166_ = crate::leanh::lean_ctor_get(v___x_3165_, 0);
                    crate::leanh::lean_inc(v_a_3166_);
                    crate::leanh::lean_dec_ref_known(v___x_3165_, 1);
                    v___x_3167_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_propagateForallPropUp___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_propagateForallPropUp___closed__2_once
                        ),
                        _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2,
                    );
                    crate::leanh::lean_inc_ref(v___y_3157_);
                    crate::leanh::lean_inc_ref(v_binderType_3150_);
                    v___x_3168_ = l_Lean_mkApp5(
                        v___x_3167_,
                        v_binderType_3150_,
                        v___y_3156_,
                        v___y_3157_,
                        v___y_3158_,
                        v_a_3166_,
                    );
                    v___x_3169_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                        v_e_3137_,
                        v___y_3157_,
                        v___x_3168_,
                        v___y_3155_,
                        v___y_3159_,
                        v___y_3160_,
                        v___y_3161_,
                        v___y_3162_,
                        v___y_3163_,
                        v___y_3164_,
                    );
                    return v___x_3169_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3158_);
                    crate::leanh::lean_dec_ref(v___y_3157_);
                    crate::leanh::lean_dec_ref(v___y_3156_);
                    crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                    v_a_3170_ = crate::leanh::lean_ctor_get(v___x_3165_, 0);
                    v_isSharedCheck_3177_ = (!crate::leanh::lean_is_exclusive(v___x_3165_)) as u8;
                    if v_isSharedCheck_3177_ == 0 {
                        v___x_3172_ = v___x_3165_;
                        v_isShared_3173_ = v_isSharedCheck_3177_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3170_);
                        crate::leanh::lean_dec(v___x_3165_);
                        v___x_3172_ = crate::leanh::lean_box(0);
                        v_isShared_3173_ = v_isSharedCheck_3177_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3173_ == 0 {
                    v___x_3175_ = v___x_3172_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3176_, 0, v_a_3170_);
                    v___x_3175_ = v_reuseFailAlloc_3176_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3175_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v_binderType_3150_);
                v___x_3192_ = l_Lean_Meta_Grind_mkEqTrueProof(
                    v_binderType_3150_,
                    v___y_3182_,
                    v___y_3183_,
                    v___y_3184_,
                    v___y_3185_,
                    v___y_3186_,
                    v___y_3187_,
                    v___y_3188_,
                    v___y_3189_,
                    v___y_3190_,
                    v___y_3191_,
                );
                if crate::leanh::lean_obj_tag(v___x_3192_) == 0 {
                    v_a_3193_ = crate::leanh::lean_ctor_get(v___x_3192_, 0);
                    crate::leanh::lean_inc_n(v_a_3193_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3192_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_3150_);
                    v___x_3194_ = l_Lean_Meta_mkOfEqTrueCore(v_binderType_3150_, v_a_3193_);
                    v___x_3195_ = lean_expr_instantiate1(v_body_3151_, v___x_3194_);
                    crate::leanh::lean_dec_ref(v___x_3194_);
                    crate::leanh::lean_inc(v___y_3191_);
                    crate::leanh::lean_inc_ref(v___y_3190_);
                    crate::leanh::lean_inc(v___y_3189_);
                    crate::leanh::lean_inc_ref(v___y_3188_);
                    crate::leanh::lean_inc(v___y_3187_);
                    crate::leanh::lean_inc_ref(v___y_3186_);
                    crate::leanh::lean_inc(v___y_3185_);
                    crate::leanh::lean_inc_ref(v___y_3184_);
                    crate::leanh::lean_inc(v___y_3183_);
                    crate::leanh::lean_inc(v___y_3182_);
                    v___x_3196_ = lean_grind_preprocess(
                        v___x_3195_,
                        v___y_3182_,
                        v___y_3183_,
                        v___y_3184_,
                        v___y_3185_,
                        v___y_3186_,
                        v___y_3187_,
                        v___y_3188_,
                        v___y_3189_,
                        v___y_3190_,
                        v___y_3191_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3196_) == 0 {
                        v_a_3197_ = crate::leanh::lean_ctor_get(v___x_3196_, 0);
                        crate::leanh::lean_inc(v_a_3197_);
                        crate::leanh::lean_dec_ref_known(v___x_3196_, 1);
                        v___x_3198_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_e_3137_, v___y_3182_);
                        if crate::leanh::lean_obj_tag(v___x_3198_) == 0 {
                            v_a_3199_ = crate::leanh::lean_ctor_get(v___x_3198_, 0);
                            crate::leanh::lean_inc(v_a_3199_);
                            crate::leanh::lean_dec_ref_known(v___x_3198_, 1);
                            v_expr_3200_ = crate::leanh::lean_ctor_get(v_a_3197_, 0);
                            crate::leanh::lean_inc_ref_n(v_expr_3200_, 2);
                            v___x_3201_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_3191_);
                            crate::leanh::lean_inc_ref(v___y_3190_);
                            crate::leanh::lean_inc(v___y_3189_);
                            crate::leanh::lean_inc_ref(v___y_3188_);
                            crate::leanh::lean_inc(v___y_3187_);
                            crate::leanh::lean_inc_ref(v___y_3186_);
                            crate::leanh::lean_inc(v___y_3185_);
                            crate::leanh::lean_inc_ref(v___y_3184_);
                            crate::leanh::lean_inc(v___y_3183_);
                            crate::leanh::lean_inc(v___y_3182_);
                            v___x_3202_ = lean_grind_internalize(
                                v_expr_3200_,
                                v_a_3199_,
                                v___x_3201_,
                                v___y_3182_,
                                v___y_3183_,
                                v___y_3184_,
                                v___y_3185_,
                                v___y_3186_,
                                v___y_3187_,
                                v___y_3188_,
                                v___y_3189_,
                                v___y_3190_,
                                v___y_3191_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3202_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3202_, 1);
                                v_options_3203_ = crate::leanh::lean_ctor_get(v___y_3190_, 2);
                                v_inheritedTraceOptions_3204_ =
                                    crate::leanh::lean_ctor_get(v___y_3190_, 13);
                                v_hasTrace_3205_ = crate::leanh::lean_ctor_get_uint8(
                                    v_options_3203_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                                        as u32,
                                );
                                crate::leanh::lean_inc_ref(v_body_3151_);
                                crate::leanh::lean_inc_ref(v_binderType_3150_);
                                crate::leanh::lean_inc(v_binderName_3149_);
                                v___x_3206_ = l_Lean_mkLambda(
                                    v_binderName_3149_,
                                    v_binderInfo_3152_,
                                    v_binderType_3150_,
                                    v_body_3151_,
                                );
                                if v_hasTrace_3205_ == 0 {
                                    v___y_3154_ = v_a_3197_;
                                    v___y_3155_ = v___y_3181_;
                                    v___y_3156_ = v___x_3206_;
                                    v___y_3157_ = v_expr_3200_;
                                    v___y_3158_ = v_a_3193_;
                                    v___y_3159_ = v___y_3182_;
                                    v___y_3160_ = v___y_3184_;
                                    v___y_3161_ = v___y_3188_;
                                    v___y_3162_ = v___y_3189_;
                                    v___y_3163_ = v___y_3190_;
                                    v___y_3164_ = v___y_3191_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3207_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropUp___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropUp___closed__7_once), _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
                                    v___x_3208_ =
                                        l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                            v_inheritedTraceOptions_3204_,
                                            v_options_3203_,
                                            v___x_3207_,
                                        );
                                    if v___x_3208_ == 0 {
                                        v___y_3154_ = v_a_3197_;
                                        v___y_3155_ = v___y_3181_;
                                        v___y_3156_ = v___x_3206_;
                                        v___y_3157_ = v_expr_3200_;
                                        v___y_3158_ = v_a_3193_;
                                        v___y_3159_ = v___y_3182_;
                                        v___y_3160_ = v___y_3184_;
                                        v___y_3161_ = v___y_3188_;
                                        v___y_3162_ = v___y_3189_;
                                        v___y_3163_ = v___y_3190_;
                                        v___y_3164_ = v___y_3191_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3209_ = l_Lean_Meta_Grind_updateLastTag(
                                            v___y_3182_,
                                            v___y_3183_,
                                            v___y_3184_,
                                            v___y_3185_,
                                            v___y_3186_,
                                            v___y_3187_,
                                            v___y_3188_,
                                            v___y_3189_,
                                            v___y_3190_,
                                            v___y_3191_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_3209_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3209_, 1);
                                            v___x_3210_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropUp___closed__9), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropUp___closed__9_once), _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
                                            crate::leanh::lean_inc_ref(v_expr_3200_);
                                            v___x_3211_ = l_Lean_MessageData_ofExpr(v_expr_3200_);
                                            v___x_3212_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3212_,
                                                0,
                                                v___x_3210_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3212_,
                                                1,
                                                v___x_3211_,
                                            );
                                            v___x_3213_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropUp___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropUp___closed__11_once), _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
                                            v___x_3214_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3214_,
                                                0,
                                                v___x_3212_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3214_,
                                                1,
                                                v___x_3213_,
                                            );
                                            crate::leanh::lean_inc_ref(v_e_3137_);
                                            v___x_3215_ = l_Lean_indentExpr(v_e_3137_);
                                            v___x_3216_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3216_,
                                                0,
                                                v___x_3214_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3216_,
                                                1,
                                                v___x_3215_,
                                            );
                                            v___x_3217_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_3179_, v___x_3216_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
                                            if crate::leanh::lean_obj_tag(v___x_3217_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3217_, 1);
                                                v___y_3154_ = v_a_3197_;
                                                v___y_3155_ = v___y_3181_;
                                                v___y_3156_ = v___x_3206_;
                                                v___y_3157_ = v_expr_3200_;
                                                v___y_3158_ = v_a_3193_;
                                                v___y_3159_ = v___y_3182_;
                                                v___y_3160_ = v___y_3184_;
                                                v___y_3161_ = v___y_3188_;
                                                v___y_3162_ = v___y_3189_;
                                                v___y_3163_ = v___y_3190_;
                                                v___y_3164_ = v___y_3191_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3206_);
                                                crate::leanh::lean_dec_ref(v_expr_3200_);
                                                crate::leanh::lean_dec(v_a_3197_);
                                                crate::leanh::lean_dec(v_a_3193_);
                                                crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                                                return v___x_3217_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3206_);
                                            crate::leanh::lean_dec_ref(v_expr_3200_);
                                            crate::leanh::lean_dec(v_a_3197_);
                                            crate::leanh::lean_dec(v_a_3193_);
                                            crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                                            return v___x_3209_;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_expr_3200_);
                                crate::leanh::lean_dec(v_a_3197_);
                                crate::leanh::lean_dec(v_a_3193_);
                                crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                                return v___x_3202_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3197_);
                            crate::leanh::lean_dec(v_a_3193_);
                            crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                            v_a_3218_ = crate::leanh::lean_ctor_get(v___x_3198_, 0);
                            v_isSharedCheck_3225_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3198_)) as u8;
                            if v_isSharedCheck_3225_ == 0 {
                                v___x_3220_ = v___x_3198_;
                                v_isShared_3221_ = v_isSharedCheck_3225_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3218_);
                                crate::leanh::lean_dec(v___x_3198_);
                                v___x_3220_ = crate::leanh::lean_box(0);
                                v_isShared_3221_ = v_isSharedCheck_3225_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3193_);
                        crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                        v_a_3226_ = crate::leanh::lean_ctor_get(v___x_3196_, 0);
                        v_isSharedCheck_3233_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3196_)) as u8;
                        if v_isSharedCheck_3233_ == 0 {
                            v___x_3228_ = v___x_3196_;
                            v_isShared_3229_ = v_isSharedCheck_3233_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3226_);
                            crate::leanh::lean_dec(v___x_3196_);
                            v___x_3228_ = crate::leanh::lean_box(0);
                            v_isShared_3229_ = v_isSharedCheck_3233_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                    v_a_3234_ = crate::leanh::lean_ctor_get(v___x_3192_, 0);
                    v_isSharedCheck_3241_ = (!crate::leanh::lean_is_exclusive(v___x_3192_)) as u8;
                    if v_isSharedCheck_3241_ == 0 {
                        v___x_3236_ = v___x_3192_;
                        v_isShared_3237_ = v_isSharedCheck_3241_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3234_);
                        crate::leanh::lean_dec(v___x_3192_);
                        v___x_3236_ = crate::leanh::lean_box(0);
                        v_isShared_3237_ = v_isSharedCheck_3241_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3221_ == 0 {
                    v___x_3223_ = v___x_3220_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3223_;
            }
            7 => {
                if v_isShared_3229_ == 0 {
                    v___x_3231_ = v___x_3228_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
                    v___x_3231_ = v_reuseFailAlloc_3232_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3231_;
            }
            9 => {
                if v_isShared_3237_ == 0 {
                    v___x_3239_ = v___x_3236_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3240_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
                    v___x_3239_ = v_reuseFailAlloc_3240_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3239_;
            }
            11 => {
                v___x_3253_ = l_Lean_Expr_hasLooseBVars(v_body_3151_);
                if v___x_3253_ == 0 {
                    crate::leanh::lean_inc_ref(v_body_3151_);
                    crate::leanh::lean_inc_ref(v_binderType_3150_);
                    v___x_3254_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(v_e_3137_, v_binderType_3150_, v_body_3151_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
                    return v___x_3254_;
                } else {
                    crate::leanh::lean_inc_ref(v_binderType_3150_);
                    v___x_3255_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                        v_binderType_3150_,
                        v___y_3243_,
                        v___y_3247_,
                        v___y_3249_,
                        v___y_3250_,
                        v___y_3251_,
                        v___y_3252_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3255_) == 0 {
                        v_a_3256_ = crate::leanh::lean_ctor_get(v___x_3255_, 0);
                        v_isSharedCheck_3275_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3255_)) as u8;
                        if v_isSharedCheck_3275_ == 0 {
                            v___x_3258_ = v___x_3255_;
                            v_isShared_3259_ = v_isSharedCheck_3275_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3256_);
                            crate::leanh::lean_dec(v___x_3255_);
                            v___x_3258_ = crate::leanh::lean_box(0);
                            v_isShared_3259_ = v_isSharedCheck_3275_;
                            state = 12;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                        v_a_3276_ = crate::leanh::lean_ctor_get(v___x_3255_, 0);
                        v_isSharedCheck_3283_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3255_)) as u8;
                        if v_isSharedCheck_3283_ == 0 {
                            v___x_3278_ = v___x_3255_;
                            v_isShared_3279_ = v_isSharedCheck_3283_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3276_);
                            crate::leanh::lean_dec(v___x_3255_);
                            v___x_3278_ = crate::leanh::lean_box(0);
                            v_isShared_3279_ = v_isSharedCheck_3283_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_3260_ = (crate::leanh::lean_unbox(v_a_3256_) as u8);
                crate::leanh::lean_dec(v_a_3256_);
                if v___x_3260_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                    v___x_3261_ = crate::leanh::lean_box(0);
                    if v_isShared_3259_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3258_, 0, v___x_3261_);
                        v___x_3263_ = v___x_3258_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
                        v___x_3263_ = v_reuseFailAlloc_3264_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3258_);
                    v_inheritedTraceOptions_3265_ = crate::leanh::lean_ctor_get(v___y_3251_, 13);
                    v___x_3266_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0(
                        v_cls_3179_,
                        v_inheritedTraceOptions_3265_,
                        v___y_3243_,
                        v___y_3244_,
                        v___y_3245_,
                        v___y_3246_,
                        v___y_3247_,
                        v___y_3248_,
                        v___y_3249_,
                        v___y_3250_,
                        v___y_3251_,
                        v___y_3252_,
                    );
                    v_a_3267_ = crate::leanh::lean_ctor_get(v___x_3266_, 0);
                    crate::leanh::lean_inc(v_a_3267_);
                    crate::leanh::lean_dec_ref(v___x_3266_);
                    v___x_3268_ = 0;
                    v___x_3269_ = (crate::leanh::lean_unbox(v_a_3267_) as u8);
                    crate::leanh::lean_dec(v_a_3267_);
                    if v___x_3269_ == 0 {
                        v___y_3181_ = v___x_3268_;
                        v___y_3182_ = v___y_3243_;
                        v___y_3183_ = v___y_3244_;
                        v___y_3184_ = v___y_3245_;
                        v___y_3185_ = v___y_3246_;
                        v___y_3186_ = v___y_3247_;
                        v___y_3187_ = v___y_3248_;
                        v___y_3188_ = v___y_3249_;
                        v___y_3189_ = v___y_3250_;
                        v___y_3190_ = v___y_3251_;
                        v___y_3191_ = v___y_3252_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3270_ = l_Lean_Meta_Grind_updateLastTag(
                            v___y_3243_,
                            v___y_3244_,
                            v___y_3245_,
                            v___y_3246_,
                            v___y_3247_,
                            v___y_3248_,
                            v___y_3249_,
                            v___y_3250_,
                            v___y_3251_,
                            v___y_3252_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3270_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3270_, 1);
                            v___x_3271_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateForallPropUp___closed__13
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateForallPropUp___closed__13_once
                                ),
                                _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13,
                            );
                            crate::leanh::lean_inc_ref(v_e_3137_);
                            v___x_3272_ = l_Lean_MessageData_ofExpr(v_e_3137_);
                            v___x_3273_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3273_, 0, v___x_3271_);
                            crate::leanh::lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                            v___x_3274_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(v_cls_3179_, v___x_3273_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_);
                            if crate::leanh::lean_obj_tag(v___x_3274_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3274_, 1);
                                v___y_3181_ = v___x_3268_;
                                v___y_3182_ = v___y_3243_;
                                v___y_3183_ = v___y_3244_;
                                v___y_3184_ = v___y_3245_;
                                v___y_3185_ = v___y_3246_;
                                v___y_3186_ = v___y_3247_;
                                v___y_3187_ = v___y_3248_;
                                v___y_3188_ = v___y_3249_;
                                v___y_3189_ = v___y_3250_;
                                v___y_3190_ = v___y_3251_;
                                v___y_3191_ = v___y_3252_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                                return v___x_3274_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_e_3137_, 3);
                            return v___x_3270_;
                        }
                    }
                }
            }
            13 => {
                return v___x_3263_;
            }
            14 => {
                if v_isShared_3279_ == 0 {
                    v___x_3281_ = v___x_3278_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
                    v___x_3281_ = v_reuseFailAlloc_3282_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateForallPropUp___boxed(
    mut v_e_3292_: *mut crate::leanh::LeanObject,
    mut v_a_3293_: *mut crate::leanh::LeanObject,
    mut v_a_3294_: *mut crate::leanh::LeanObject,
    mut v_a_3295_: *mut crate::leanh::LeanObject,
    mut v_a_3296_: *mut crate::leanh::LeanObject,
    mut v_a_3297_: *mut crate::leanh::LeanObject,
    mut v_a_3298_: *mut crate::leanh::LeanObject,
    mut v_a_3299_: *mut crate::leanh::LeanObject,
    mut v_a_3300_: *mut crate::leanh::LeanObject,
    mut v_a_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3304_ = l_Lean_Meta_Grind_propagateForallPropUp(
        v_e_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_,
        v_a_3300_, v_a_3301_, v_a_3302_,
    );
    crate::leanh::lean_dec(v_a_3302_);
    crate::leanh::lean_dec_ref(v_a_3301_);
    crate::leanh::lean_dec(v_a_3300_);
    crate::leanh::lean_dec_ref(v_a_3299_);
    crate::leanh::lean_dec(v_a_3298_);
    crate::leanh::lean_dec_ref(v_a_3297_);
    crate::leanh::lean_dec(v_a_3296_);
    crate::leanh::lean_dec_ref(v_a_3295_);
    crate::leanh::lean_dec(v_a_3294_);
    crate::leanh::lean_dec(v_a_3293_);
    return v_res_3304_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(
    mut v_cls_3305_: *mut crate::leanh::LeanObject,
    mut v_msg_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3318_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(
        v_cls_3305_,
        v_msg_3306_,
        v___y_3313_,
        v___y_3314_,
        v___y_3315_,
        v___y_3316_,
    );
    return v___x_3318_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(
    mut v_cls_3319_: *mut crate::leanh::LeanObject,
    mut v_msg_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3332_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(
        v_cls_3319_,
        v_msg_3320_,
        v___y_3321_,
        v___y_3322_,
        v___y_3323_,
        v___y_3324_,
        v___y_3325_,
        v___y_3326_,
        v___y_3327_,
        v___y_3328_,
        v___y_3329_,
        v___y_3330_,
    );
    crate::leanh::lean_dec(v___y_3330_);
    crate::leanh::lean_dec_ref(v___y_3329_);
    crate::leanh::lean_dec(v___y_3328_);
    crate::leanh::lean_dec_ref(v___y_3327_);
    crate::leanh::lean_dec(v___y_3326_);
    crate::leanh::lean_dec_ref(v___y_3325_);
    crate::leanh::lean_dec(v___y_3324_);
    crate::leanh::lean_dec_ref(v___y_3323_);
    crate::leanh::lean_dec(v___y_3322_);
    crate::leanh::lean_dec(v___y_3321_);
    return v_res_3332_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(
    mut v_origin_3335_: *mut crate::leanh::LeanObject,
    mut v_proof_3336_: *mut crate::leanh::LeanObject,
    mut v_kind_3337_: *mut crate::leanh::LeanObject,
    mut v_prios_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: u8 = 0;
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3350_: u8 = 0;
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3353_: u8 = 0;
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3358_: u8 = 0;
    let mut v_unused_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: u8 = 0;
    let mut v___x_3361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3344_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
                v___x_3345_ = 0;
                v___x_3346_ = 1;
                v___x_3347_ = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(
                    v_origin_3335_,
                    v___x_3344_,
                    v_proof_3336_,
                    v_kind_3337_,
                    v_prios_3338_,
                    v___x_3345_,
                    v___x_3345_,
                    v___x_3346_,
                    v_a_3339_,
                    v_a_3340_,
                    v_a_3341_,
                    v_a_3342_,
                );
                if crate::leanh::lean_obj_tag(v___x_3347_) == 0 {
                    return v___x_3347_;
                } else {
                    v_a_3348_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                    crate::leanh::lean_inc(v_a_3348_);
                    v___x_3360_ = l_Lean_Exception_isInterrupt(v_a_3348_);
                    if v___x_3360_ == 0 {
                        v___x_3361_ = l_Lean_Exception_isRuntime(v_a_3348_);
                        v___y_3350_ = v___x_3361_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_3348_);
                        v___y_3350_ = v___x_3360_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3350_ == 0 {
                    v_isSharedCheck_3358_ = (!crate::leanh::lean_is_exclusive(v___x_3347_)) as u8;
                    if v_isSharedCheck_3358_ == 0 {
                        v_unused_3359_ = crate::leanh::lean_ctor_get(v___x_3347_, 0);
                        crate::leanh::lean_dec(v_unused_3359_);
                        v___x_3352_ = v___x_3347_;
                        v_isShared_3353_ = v_isSharedCheck_3358_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3347_);
                        v___x_3352_ = crate::leanh::lean_box(0);
                        v_isShared_3353_ = v_isSharedCheck_3358_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___x_3347_;
                }
            }
            2 => {
                v___x_3354_ = crate::leanh::lean_box(0);
                if v_isShared_3353_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3352_, 0);
                    crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3354_);
                    v___x_3356_ = v___x_3352_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3357_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
                    v___x_3356_ = v_reuseFailAlloc_3357_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(
    mut v_origin_3362_: *mut crate::leanh::LeanObject,
    mut v_proof_3363_: *mut crate::leanh::LeanObject,
    mut v_kind_3364_: *mut crate::leanh::LeanObject,
    mut v_prios_3365_: *mut crate::leanh::LeanObject,
    mut v_a_3366_: *mut crate::leanh::LeanObject,
    mut v_a_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3371_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_origin_3362_, v_proof_3363_, v_kind_3364_, v_prios_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_);
    crate::leanh::lean_dec(v_a_3369_);
    crate::leanh::lean_dec_ref(v_a_3368_);
    crate::leanh::lean_dec(v_a_3367_);
    crate::leanh::lean_dec_ref(v_a_3366_);
    return v_res_3371_;
}
pub unsafe fn l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(
    mut v_x_3372_: *mut crate::leanh::LeanObject,
    mut v_x_3373_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: u8 = 0;
    let mut v___x_3376_: u8 = 0;
    let mut v_head_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3372_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_3373_) == 0 {
                        v___x_3374_ = 1;
                        return v___x_3374_;
                    } else {
                        v___x_3375_ = 0;
                        return v___x_3375_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_3373_) == 0 {
                        v___x_3376_ = 0;
                        return v___x_3376_;
                    } else {
                        v_head_3377_ = crate::leanh::lean_ctor_get(v_x_3372_, 0);
                        v_tail_3378_ = crate::leanh::lean_ctor_get(v_x_3372_, 1);
                        v_head_3379_ = crate::leanh::lean_ctor_get(v_x_3373_, 0);
                        v_tail_3380_ = crate::leanh::lean_ctor_get(v_x_3373_, 1);
                        v___x_3381_ = lean_expr_eqv(v_head_3377_, v_head_3379_);
                        if v___x_3381_ == 0 {
                            return v___x_3381_;
                        } else {
                            v_x_3372_ = v_tail_3378_;
                            v_x_3373_ = v_tail_3380_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(
    mut v_x_3383_: *mut crate::leanh::LeanObject,
    mut v_x_3384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3385_: u8 = 0;
    let mut v_r_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3385_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_x_3383_, v_x_3384_);
    crate::leanh::lean_dec(v_x_3384_);
    crate::leanh::lean_dec(v_x_3383_);
    v_r_3386_ = crate::leanh::lean_box((v_res_3385_) as usize);
    return v_r_3386_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(
    mut v_thm_x27_3387_: *mut crate::leanh::LeanObject,
    mut v_as_3388_: *mut crate::leanh::LeanObject,
    mut v_i_3389_: usize,
    mut v_stop_3390_: usize,
) -> u8 {
    let mut v___x_3391_: u8 = 0;
    let mut v_patterns_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: usize = 0;
    let mut v___x_3396_: usize = 0;
    let mut v___x_3398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3391_ = lean_usize_dec_eq(v_i_3389_, v_stop_3390_);
                if v___x_3391_ == 0 {
                    v_patterns_3392_ = crate::leanh::lean_ctor_get(v_thm_x27_3387_, 3);
                    v___x_3393_ = lean_array_uget_borrowed(v_as_3388_, v_i_3389_);
                    v___x_3394_ = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(v_patterns_3392_, v___x_3393_);
                    if v___x_3394_ == 0 {
                        v___x_3395_ = 1usize;
                        v___x_3396_ = lean_usize_add(v_i_3389_, v___x_3395_);
                        v_i_3389_ = v___x_3396_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3394_;
                    }
                } else {
                    v___x_3398_ = 0;
                    return v___x_3398_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(
    mut v_thm_x27_3399_: *mut crate::leanh::LeanObject,
    mut v_as_3400_: *mut crate::leanh::LeanObject,
    mut v_i_3401_: *mut crate::leanh::LeanObject,
    mut v_stop_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3403_: usize = 0;
    let mut v_stop_boxed_3404_: usize = 0;
    let mut v_res_3405_: u8 = 0;
    let mut v_r_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3403_ = crate::leanh::lean_unbox_usize(v_i_3401_);
    crate::leanh::lean_dec(v_i_3401_);
    v_stop_boxed_3404_ = crate::leanh::lean_unbox_usize(v_stop_3402_);
    crate::leanh::lean_dec(v_stop_3402_);
    v_res_3405_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_3399_, v_as_3400_, v_i_boxed_3403_, v_stop_boxed_3404_);
    crate::leanh::lean_dec_ref(v_as_3400_);
    crate::leanh::lean_dec_ref(v_thm_x27_3399_);
    v_r_3406_ = crate::leanh::lean_box((v_res_3405_) as usize);
    return v_r_3406_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(
    mut v_patternsFoundSoFar_3407_: *mut crate::leanh::LeanObject,
    mut v_thm_x27_3408_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: u8 = 0;
    v___x_3409_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3410_ = lean_array_get_size(v_patternsFoundSoFar_3407_);
    v___x_3411_ = lean_nat_dec_lt(v___x_3409_, v___x_3410_);
    if v___x_3411_ == 0 {
        let mut v___x_3412_: u8 = 0;
        v___x_3412_ = 1;
        return v___x_3412_;
    } else {
        if v___x_3411_ == 0 {
            return v___x_3411_;
        } else {
            let mut v___x_3413_: usize = 0;
            let mut v___x_3414_: usize = 0;
            let mut v___x_3415_: u8 = 0;
            v___x_3413_ = 0usize;
            v___x_3414_ = lean_usize_of_nat(v___x_3410_);
            v___x_3415_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(v_thm_x27_3408_, v_patternsFoundSoFar_3407_, v___x_3413_, v___x_3414_);
            if v___x_3415_ == 0 {
                return v___x_3411_;
            } else {
                let mut v___x_3416_: u8 = 0;
                v___x_3416_ = 0;
                return v___x_3416_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(
    mut v_patternsFoundSoFar_3417_: *mut crate::leanh::LeanObject,
    mut v_thm_x27_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3419_: u8 = 0;
    let mut v_r_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3419_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(
        v_patternsFoundSoFar_3417_,
        v_thm_x27_3418_,
    );
    crate::leanh::lean_dec_ref(v_thm_x27_3418_);
    crate::leanh::lean_dec_ref(v_patternsFoundSoFar_3417_);
    v_r_3420_ = crate::leanh::lean_box((v_res_3419_) as usize);
    return v_r_3420_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(
    mut v_proof_3432_: *mut crate::leanh::LeanObject,
    mut v_a_3433_: *mut crate::leanh::LeanObject,
    mut v_a_3434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3440_: u8 = 0;
    let mut v___y_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarId_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3454_: u8 = 0;
    let mut v_nextDeclIdx_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enodeMap_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_parents_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrTable_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appMap_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesFound_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newFacts_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inconsistent_3463_: u8 = 0;
    let mut v_nextIdx_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newRawFacts_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facts_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extThms_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inj_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_split_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_clean_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sstates_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v_thmMap_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_gmt_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thms_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newThms_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numInstances_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDelayedInstances_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preInstances_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextThmIdx_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchEqNames_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_delayedThmInsts_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3507_: u8 = 0;
    let mut v_isSharedCheck_3508_: u8 = 0;
    let mut v_unused_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3510_: u8 = 0;
    let mut v_unused_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: u8 = 0;
    let mut v_arg_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: u8 = 0;
    let mut v___x_3520_: u8 = 0;
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v_isSharedCheck_3528_: u8 = 0;
    let mut v_a_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3532_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_proof_3432_);
                v___x_3436_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_proof_3432_, v_a_3434_);
                if crate::leanh::lean_obj_tag(v___x_3436_) == 0 {
                    v_a_3437_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                    v_isSharedCheck_3528_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                    if v_isSharedCheck_3528_ == 0 {
                        v___x_3439_ = v___x_3436_;
                        v_isShared_3440_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3437_);
                        crate::leanh::lean_dec(v___x_3436_);
                        v___x_3439_ = crate::leanh::lean_box(0);
                        v_isShared_3440_ = v_isSharedCheck_3528_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_proof_3432_);
                    v_a_3529_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                    v_isSharedCheck_3536_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                    if v_isSharedCheck_3536_ == 0 {
                        v___x_3531_ = v___x_3436_;
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3529_);
                        crate::leanh::lean_dec(v___x_3436_);
                        v___x_3531_ = crate::leanh::lean_box(0);
                        v_isShared_3532_ = v_isSharedCheck_3536_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3512_ = l_Lean_Expr_cleanupAnnotations(v_a_3437_);
                v___x_3513_ = l_Lean_Expr_isApp(v___x_3512_);
                if v___x_3513_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3512_);
                    v___y_3442_ = v_a_3433_;
                    state = 2;
                    continue;
                } else {
                    v_arg_3514_ = crate::leanh::lean_ctor_get(v___x_3512_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3514_);
                    v___x_3515_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3512_);
                    v___x_3516_ = l_Lean_Expr_isApp(v___x_3515_);
                    if v___x_3516_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3515_);
                        crate::leanh::lean_dec_ref(v_arg_3514_);
                        v___y_3442_ = v_a_3433_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3515_);
                        v___x_3518_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__3;
                        v___x_3519_ = l_Lean_Expr_isConstOf(v___x_3517_, v___x_3518_);
                        if v___x_3519_ == 0 {
                            v___x_3520_ = l_Lean_Expr_isApp(v___x_3517_);
                            if v___x_3520_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3517_);
                                crate::leanh::lean_dec_ref(v_arg_3514_);
                                v___y_3442_ = v_a_3433_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3521_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3517_);
                                v___x_3522_ = l_Lean_Expr_isApp(v___x_3521_);
                                if v___x_3522_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_3521_);
                                    crate::leanh::lean_dec_ref(v_arg_3514_);
                                    v___y_3442_ = v_a_3433_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_3523_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3521_);
                                    v___x_3524_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__6;
                                    v___x_3525_ = l_Lean_Expr_isConstOf(v___x_3523_, v___x_3524_);
                                    crate::leanh::lean_dec_ref(v___x_3523_);
                                    if v___x_3525_ == 0 {
                                        crate::leanh::lean_dec_ref(v_arg_3514_);
                                        v___y_3442_ = v_a_3433_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_del_object(v___x_3439_);
                                        crate::leanh::lean_dec_ref(v_proof_3432_);
                                        v_proof_3432_ = v_arg_3514_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3517_);
                            crate::leanh::lean_del_object(v___x_3439_);
                            crate::leanh::lean_dec_ref(v_proof_3432_);
                            v_proof_3432_ = v_arg_3514_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_proof_3432_) == 1 {
                    v_fvarId_3443_ = crate::leanh::lean_ctor_get(v_proof_3432_, 0);
                    crate::leanh::lean_inc(v_fvarId_3443_);
                    crate::leanh::lean_dec_ref_known(v_proof_3432_, 1);
                    v___x_3444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3444_, 0, v_fvarId_3443_);
                    if v_isShared_3440_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3439_, 0, v___x_3444_);
                        v___x_3446_ = v___x_3439_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3447_, 0, v___x_3444_);
                        v___x_3446_ = v_reuseFailAlloc_3447_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_proof_3432_);
                    v___x_3448_ = lean_st_ref_take(v___y_3442_);
                    v_toGoalState_3449_ = crate::leanh::lean_ctor_get(v___x_3448_, 0);
                    crate::leanh::lean_inc_ref(v_toGoalState_3449_);
                    v_ematch_3450_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 12);
                    crate::leanh::lean_inc_ref(v_ematch_3450_);
                    v_mvarId_3451_ = crate::leanh::lean_ctor_get(v___x_3448_, 1);
                    v_isSharedCheck_3510_ = (!crate::leanh::lean_is_exclusive(v___x_3448_)) as u8;
                    if v_isSharedCheck_3510_ == 0 {
                        v_unused_3511_ = crate::leanh::lean_ctor_get(v___x_3448_, 0);
                        crate::leanh::lean_dec(v_unused_3511_);
                        v___x_3453_ = v___x_3448_;
                        v_isShared_3454_ = v_isSharedCheck_3510_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_mvarId_3451_);
                        crate::leanh::lean_dec(v___x_3448_);
                        v___x_3453_ = crate::leanh::lean_box(0);
                        v_isShared_3454_ = v_isSharedCheck_3510_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3446_;
            }
            4 => {
                v_nextDeclIdx_3455_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 0);
                v_enodeMap_3456_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 1);
                v_exprs_3457_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 2);
                v_parents_3458_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 3);
                v_congrTable_3459_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 4);
                v_appMap_3460_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 5);
                v_indicesFound_3461_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 6);
                v_newFacts_3462_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 7);
                v_inconsistent_3463_ = crate::leanh::lean_ctor_get_uint8(
                    v_toGoalState_3449_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                );
                v_nextIdx_3464_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 8);
                v_newRawFacts_3465_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 9);
                v_facts_3466_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 10);
                v_extThms_3467_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 11);
                v_inj_3468_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 13);
                v_split_3469_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 14);
                v_clean_3470_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 15);
                v_sstates_3471_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 16);
                v_isSharedCheck_3508_ =
                    (!crate::leanh::lean_is_exclusive(v_toGoalState_3449_)) as u8;
                if v_isSharedCheck_3508_ == 0 {
                    v_unused_3509_ = crate::leanh::lean_ctor_get(v_toGoalState_3449_, 12);
                    crate::leanh::lean_dec(v_unused_3509_);
                    v___x_3473_ = v_toGoalState_3449_;
                    v_isShared_3474_ = v_isSharedCheck_3508_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_sstates_3471_);
                    crate::leanh::lean_inc(v_clean_3470_);
                    crate::leanh::lean_inc(v_split_3469_);
                    crate::leanh::lean_inc(v_inj_3468_);
                    crate::leanh::lean_inc(v_extThms_3467_);
                    crate::leanh::lean_inc(v_facts_3466_);
                    crate::leanh::lean_inc(v_newRawFacts_3465_);
                    crate::leanh::lean_inc(v_nextIdx_3464_);
                    crate::leanh::lean_inc(v_newFacts_3462_);
                    crate::leanh::lean_inc(v_indicesFound_3461_);
                    crate::leanh::lean_inc(v_appMap_3460_);
                    crate::leanh::lean_inc(v_congrTable_3459_);
                    crate::leanh::lean_inc(v_parents_3458_);
                    crate::leanh::lean_inc(v_exprs_3457_);
                    crate::leanh::lean_inc(v_enodeMap_3456_);
                    crate::leanh::lean_inc(v_nextDeclIdx_3455_);
                    crate::leanh::lean_dec(v_toGoalState_3449_);
                    v___x_3473_ = crate::leanh::lean_box(0);
                    v_isShared_3474_ = v_isSharedCheck_3508_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_thmMap_3475_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 0);
                v_gmt_3476_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 1);
                v_thms_3477_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 2);
                v_newThms_3478_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 3);
                v_numInstances_3479_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 4);
                v_numDelayedInstances_3480_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 5);
                v_num_3481_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 6);
                v_preInstances_3482_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 7);
                v_nextThmIdx_3483_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 8);
                v_matchEqNames_3484_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 9);
                v_delayedThmInsts_3485_ = crate::leanh::lean_ctor_get(v_ematch_3450_, 10);
                v_isSharedCheck_3507_ = (!crate::leanh::lean_is_exclusive(v_ematch_3450_)) as u8;
                if v_isSharedCheck_3507_ == 0 {
                    v___x_3487_ = v_ematch_3450_;
                    v_isShared_3488_ = v_isSharedCheck_3507_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_delayedThmInsts_3485_);
                    crate::leanh::lean_inc(v_matchEqNames_3484_);
                    crate::leanh::lean_inc(v_nextThmIdx_3483_);
                    crate::leanh::lean_inc(v_preInstances_3482_);
                    crate::leanh::lean_inc(v_num_3481_);
                    crate::leanh::lean_inc(v_numDelayedInstances_3480_);
                    crate::leanh::lean_inc(v_numInstances_3479_);
                    crate::leanh::lean_inc(v_newThms_3478_);
                    crate::leanh::lean_inc(v_thms_3477_);
                    crate::leanh::lean_inc(v_gmt_3476_);
                    crate::leanh::lean_inc(v_thmMap_3475_);
                    crate::leanh::lean_dec(v_ematch_3450_);
                    v___x_3487_ = crate::leanh::lean_box(0);
                    v_isShared_3488_ = v_isSharedCheck_3507_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3489_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3490_ = lean_nat_add(v_nextThmIdx_3483_, v___x_3489_);
                if v_isShared_3488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3487_, 8, v___x_3490_);
                    v___x_3492_ = v___x_3487_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3506_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_thmMap_3475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 1, v_gmt_3476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 2, v_thms_3477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 3, v_newThms_3478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 4, v_numInstances_3479_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3506_,
                        5,
                        v_numDelayedInstances_3480_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 6, v_num_3481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 7, v_preInstances_3482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 8, v___x_3490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3506_, 9, v_matchEqNames_3484_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3506_,
                        10,
                        v_delayedThmInsts_3485_,
                    );
                    v___x_3492_ = v_reuseFailAlloc_3506_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3474_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3473_, 12, v___x_3492_);
                    v___x_3494_ = v___x_3473_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3505_ = crate::leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_nextDeclIdx_3455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 1, v_enodeMap_3456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 2, v_exprs_3457_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 3, v_parents_3458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 4, v_congrTable_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 5, v_appMap_3460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 6, v_indicesFound_3461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 7, v_newFacts_3462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 8, v_nextIdx_3464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 9, v_newRawFacts_3465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 10, v_facts_3466_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 11, v_extThms_3467_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 12, v___x_3492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 13, v_inj_3468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 14, v_split_3469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 15, v_clean_3470_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3505_, 16, v_sstates_3471_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3505_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 17) as u32,
                        v_inconsistent_3463_,
                    );
                    v___x_3494_ = v_reuseFailAlloc_3505_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_3454_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3453_, 0, v___x_3494_);
                    v___x_3496_ = v___x_3453_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3504_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3504_, 0, v___x_3494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3504_, 1, v_mvarId_3451_);
                    v___x_3496_ = v_reuseFailAlloc_3504_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3497_ = lean_st_ref_set(v___y_3442_, v___x_3496_);
                v___x_3498_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___closed__1;
                v___x_3499_ = lean_name_append_index_after(v___x_3498_, v_nextThmIdx_3483_);
                v___x_3500_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3500_, 0, v___x_3499_);
                if v_isShared_3440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3439_, 0, v___x_3500_);
                    v___x_3502_ = v___x_3439_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v___x_3500_);
                    v___x_3502_ = v_reuseFailAlloc_3503_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3502_;
            }
            11 => {
                if v_isShared_3532_ == 0 {
                    v___x_3534_ = v___x_3531_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3535_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
                    v___x_3534_ = v_reuseFailAlloc_3535_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg___boxed(
    mut v_proof_3537_: *mut crate::leanh::LeanObject,
    mut v_a_3538_: *mut crate::leanh::LeanObject,
    mut v_a_3539_: *mut crate::leanh::LeanObject,
    mut v_a_3540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3541_ =
        l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(
            v_proof_3537_,
            v_a_3538_,
            v_a_3539_,
        );
    crate::leanh::lean_dec(v_a_3539_);
    crate::leanh::lean_dec(v_a_3538_);
    return v_res_3541_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(
    mut v_proof_3542_: *mut crate::leanh::LeanObject,
    mut v_a_3543_: *mut crate::leanh::LeanObject,
    mut v_a_3544_: *mut crate::leanh::LeanObject,
    mut v_a_3545_: *mut crate::leanh::LeanObject,
    mut v_a_3546_: *mut crate::leanh::LeanObject,
    mut v_a_3547_: *mut crate::leanh::LeanObject,
    mut v_a_3548_: *mut crate::leanh::LeanObject,
    mut v_a_3549_: *mut crate::leanh::LeanObject,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_a_3551_: *mut crate::leanh::LeanObject,
    mut v_a_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3554_ =
        l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(
            v_proof_3542_,
            v_a_3543_,
            v_a_3550_,
        );
    return v___x_3554_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___boxed(
    mut v_proof_3555_: *mut crate::leanh::LeanObject,
    mut v_a_3556_: *mut crate::leanh::LeanObject,
    mut v_a_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
    mut v_a_3559_: *mut crate::leanh::LeanObject,
    mut v_a_3560_: *mut crate::leanh::LeanObject,
    mut v_a_3561_: *mut crate::leanh::LeanObject,
    mut v_a_3562_: *mut crate::leanh::LeanObject,
    mut v_a_3563_: *mut crate::leanh::LeanObject,
    mut v_a_3564_: *mut crate::leanh::LeanObject,
    mut v_a_3565_: *mut crate::leanh::LeanObject,
    mut v_a_3566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3567_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin(
        v_proof_3555_,
        v_a_3556_,
        v_a_3557_,
        v_a_3558_,
        v_a_3559_,
        v_a_3560_,
        v_a_3561_,
        v_a_3562_,
        v_a_3563_,
        v_a_3564_,
        v_a_3565_,
    );
    crate::leanh::lean_dec(v_a_3565_);
    crate::leanh::lean_dec_ref(v_a_3564_);
    crate::leanh::lean_dec(v_a_3563_);
    crate::leanh::lean_dec_ref(v_a_3562_);
    crate::leanh::lean_dec(v_a_3561_);
    crate::leanh::lean_dec_ref(v_a_3560_);
    crate::leanh::lean_dec(v_a_3559_);
    crate::leanh::lean_dec_ref(v_a_3558_);
    crate::leanh::lean_dec(v_a_3557_);
    crate::leanh::lean_dec(v_a_3556_);
    return v_res_3567_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(
    mut v_a_3568_: u64,
    mut v_as_3569_: *mut crate::leanh::LeanObject,
    mut v_i_3570_: usize,
    mut v_stop_3571_: usize,
) -> u8 {
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: usize = 0;
    let mut v___x_3576_: usize = 0;
    let mut v___x_3578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3572_ = lean_usize_dec_eq(v_i_3570_, v_stop_3571_);
                if v___x_3572_ == 0 {
                    v___x_3573_ = lean_array_uget_borrowed(v_as_3569_, v_i_3570_);
                    v___x_3574_ = l_Lean_Meta_Grind_AnchorRef_matches(v___x_3573_, v_a_3568_);
                    if v___x_3574_ == 0 {
                        v___x_3575_ = 1usize;
                        v___x_3576_ = lean_usize_add(v_i_3570_, v___x_3575_);
                        v_i_3570_ = v___x_3576_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3574_;
                    }
                } else {
                    v___x_3578_ = 0;
                    return v___x_3578_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_as_3580_: *mut crate::leanh::LeanObject,
    mut v_i_3581_: *mut crate::leanh::LeanObject,
    mut v_stop_3582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4179__boxed_3583_: u64 = 0;
    let mut v_i_boxed_3584_: usize = 0;
    let mut v_stop_boxed_3585_: usize = 0;
    let mut v_res_3586_: u8 = 0;
    let mut v_r_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_4179__boxed_3583_ = crate::leanh::lean_unbox_uint64(v_a_3579_);
    crate::leanh::lean_dec_ref(v_a_3579_);
    v_i_boxed_3584_ = crate::leanh::lean_unbox_usize(v_i_3581_);
    crate::leanh::lean_dec(v_i_3581_);
    v_stop_boxed_3585_ = crate::leanh::lean_unbox_usize(v_stop_3582_);
    crate::leanh::lean_dec(v_stop_3582_);
    v_res_3586_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v_a_4179__boxed_3583_, v_as_3580_, v_i_boxed_3584_, v_stop_boxed_3585_);
    crate::leanh::lean_dec_ref(v_as_3580_);
    v_r_3587_ = crate::leanh::lean_box((v_res_3586_) as usize);
    return v_r_3587_;
}
pub unsafe fn l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(
    mut v_proof_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
    mut v_a_3590_: *mut crate::leanh::LeanObject,
    mut v_a_3591_: *mut crate::leanh::LeanObject,
    mut v_a_3592_: *mut crate::leanh::LeanObject,
    mut v_a_3593_: *mut crate::leanh::LeanObject,
    mut v_a_3594_: *mut crate::leanh::LeanObject,
    mut v_a_3595_: *mut crate::leanh::LeanObject,
    mut v_a_3596_: *mut crate::leanh::LeanObject,
    mut v_a_3597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3603_: u8 = 0;
    let mut v_val_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3611_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: u8 = 0;
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: usize = 0;
    let mut v___x_3624_: usize = 0;
    let mut v___x_3625_: u64 = 0;
    let mut v___x_3626_: u8 = 0;
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_a_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3639_: u8 = 0;
    let mut v_a_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_a_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3657_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3599_ = l_Lean_Meta_Grind_getAnchorRefs___redArg(v_a_3590_);
                if crate::leanh::lean_obj_tag(v___x_3599_) == 0 {
                    v_a_3600_ = crate::leanh::lean_ctor_get(v___x_3599_, 0);
                    v_isSharedCheck_3653_ = (!crate::leanh::lean_is_exclusive(v___x_3599_)) as u8;
                    if v_isSharedCheck_3653_ == 0 {
                        v___x_3602_ = v___x_3599_;
                        v_isShared_3603_ = v_isSharedCheck_3653_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3600_);
                        crate::leanh::lean_dec(v___x_3599_);
                        v___x_3602_ = crate::leanh::lean_box(0);
                        v_isShared_3603_ = v_isSharedCheck_3653_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_proof_3588_);
                    v_a_3654_ = crate::leanh::lean_ctor_get(v___x_3599_, 0);
                    v_isSharedCheck_3661_ = (!crate::leanh::lean_is_exclusive(v___x_3599_)) as u8;
                    if v_isSharedCheck_3661_ == 0 {
                        v___x_3656_ = v___x_3599_;
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3654_);
                        crate::leanh::lean_dec(v___x_3599_);
                        v___x_3656_ = crate::leanh::lean_box(0);
                        v_isShared_3657_ = v_isSharedCheck_3661_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3600_) == 1 {
                    crate::leanh::lean_del_object(v___x_3602_);
                    v_val_3604_ = crate::leanh::lean_ctor_get(v_a_3600_, 0);
                    crate::leanh::lean_inc(v_val_3604_);
                    crate::leanh::lean_dec_ref_known(v_a_3600_, 1);
                    crate::leanh::lean_inc(v_a_3597_);
                    crate::leanh::lean_inc_ref(v_a_3596_);
                    crate::leanh::lean_inc(v_a_3595_);
                    crate::leanh::lean_inc_ref(v_a_3594_);
                    v___x_3605_ =
                        lean_infer_type(v_proof_3588_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
                    if crate::leanh::lean_obj_tag(v___x_3605_) == 0 {
                        v_a_3606_ = crate::leanh::lean_ctor_get(v___x_3605_, 0);
                        crate::leanh::lean_inc(v_a_3606_);
                        crate::leanh::lean_dec_ref_known(v___x_3605_, 1);
                        v___x_3607_ = l_Lean_Meta_Grind_getAnchor(
                            v_a_3606_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_,
                            v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3607_) == 0 {
                            v_a_3608_ = crate::leanh::lean_ctor_get(v___x_3607_, 0);
                            v_isSharedCheck_3631_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3607_)) as u8;
                            if v_isSharedCheck_3631_ == 0 {
                                v___x_3610_ = v___x_3607_;
                                v_isShared_3611_ = v_isSharedCheck_3631_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3608_);
                                crate::leanh::lean_dec(v___x_3607_);
                                v___x_3610_ = crate::leanh::lean_box(0);
                                v_isShared_3611_ = v_isSharedCheck_3631_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_3604_);
                            v_a_3632_ = crate::leanh::lean_ctor_get(v___x_3607_, 0);
                            v_isSharedCheck_3639_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3607_)) as u8;
                            if v_isSharedCheck_3639_ == 0 {
                                v___x_3634_ = v___x_3607_;
                                v_isShared_3635_ = v_isSharedCheck_3639_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3632_);
                                crate::leanh::lean_dec(v___x_3607_);
                                v___x_3634_ = crate::leanh::lean_box(0);
                                v_isShared_3635_ = v_isSharedCheck_3639_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_3604_);
                        v_a_3640_ = crate::leanh::lean_ctor_get(v___x_3605_, 0);
                        v_isSharedCheck_3647_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3605_)) as u8;
                        if v_isSharedCheck_3647_ == 0 {
                            v___x_3642_ = v___x_3605_;
                            v_isShared_3643_ = v_isSharedCheck_3647_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3640_);
                            crate::leanh::lean_dec(v___x_3605_);
                            v___x_3642_ = crate::leanh::lean_box(0);
                            v_isShared_3643_ = v_isSharedCheck_3647_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3600_);
                    crate::leanh::lean_dec_ref(v_proof_3588_);
                    v___x_3648_ = 1;
                    v___x_3649_ = crate::leanh::lean_box((v___x_3648_) as usize);
                    if v_isShared_3603_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3602_, 0, v___x_3649_);
                        v___x_3651_ = v___x_3602_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3649_);
                        v___x_3651_ = v_reuseFailAlloc_3652_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3612_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3613_ = lean_array_get_size(v_val_3604_);
                v___x_3614_ = lean_nat_dec_lt(v___x_3612_, v___x_3613_);
                if v___x_3614_ == 0 {
                    crate::leanh::lean_dec(v_a_3608_);
                    crate::leanh::lean_dec(v_val_3604_);
                    v___x_3615_ = crate::leanh::lean_box((v___x_3614_) as usize);
                    if v_isShared_3611_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3615_);
                        v___x_3617_ = v___x_3610_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3618_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3615_);
                        v___x_3617_ = v_reuseFailAlloc_3618_;
                        state = 3;
                        continue;
                    }
                } else {
                    if v___x_3614_ == 0 {
                        crate::leanh::lean_dec(v_a_3608_);
                        crate::leanh::lean_dec(v_val_3604_);
                        v___x_3619_ = crate::leanh::lean_box((v___x_3614_) as usize);
                        if v_isShared_3611_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3619_);
                            v___x_3621_ = v___x_3610_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3622_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
                            v___x_3621_ = v_reuseFailAlloc_3622_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_3623_ = 0usize;
                        v___x_3624_ = lean_usize_of_nat(v___x_3613_);
                        v___x_3625_ = crate::leanh::lean_unbox_uint64(v_a_3608_);
                        crate::leanh::lean_dec(v_a_3608_);
                        v___x_3626_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(v___x_3625_, v_val_3604_, v___x_3623_, v___x_3624_);
                        crate::leanh::lean_dec(v_val_3604_);
                        v___x_3627_ = crate::leanh::lean_box((v___x_3626_) as usize);
                        if v_isShared_3611_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3627_);
                            v___x_3629_ = v___x_3610_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3630_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3627_);
                            v___x_3629_ = v_reuseFailAlloc_3630_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_3617_;
            }
            4 => {
                return v___x_3621_;
            }
            5 => {
                return v___x_3629_;
            }
            6 => {
                if v_isShared_3635_ == 0 {
                    v___x_3637_ = v___x_3634_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
                    v___x_3637_ = v_reuseFailAlloc_3638_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3637_;
            }
            8 => {
                if v_isShared_3643_ == 0 {
                    v___x_3645_ = v___x_3642_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
                    v___x_3645_ = v_reuseFailAlloc_3646_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3645_;
            }
            10 => {
                return v___x_3651_;
            }
            11 => {
                if v_isShared_3657_ == 0 {
                    v___x_3659_ = v___x_3656_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3660_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
                    v___x_3659_ = v_reuseFailAlloc_3660_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(
    mut v_proof_3662_: *mut crate::leanh::LeanObject,
    mut v_a_3663_: *mut crate::leanh::LeanObject,
    mut v_a_3664_: *mut crate::leanh::LeanObject,
    mut v_a_3665_: *mut crate::leanh::LeanObject,
    mut v_a_3666_: *mut crate::leanh::LeanObject,
    mut v_a_3667_: *mut crate::leanh::LeanObject,
    mut v_a_3668_: *mut crate::leanh::LeanObject,
    mut v_a_3669_: *mut crate::leanh::LeanObject,
    mut v_a_3670_: *mut crate::leanh::LeanObject,
    mut v_a_3671_: *mut crate::leanh::LeanObject,
    mut v_a_3672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3673_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(
        v_proof_3662_,
        v_a_3663_,
        v_a_3664_,
        v_a_3665_,
        v_a_3666_,
        v_a_3667_,
        v_a_3668_,
        v_a_3669_,
        v_a_3670_,
        v_a_3671_,
    );
    crate::leanh::lean_dec(v_a_3671_);
    crate::leanh::lean_dec_ref(v_a_3670_);
    crate::leanh::lean_dec(v_a_3669_);
    crate::leanh::lean_dec_ref(v_a_3668_);
    crate::leanh::lean_dec(v_a_3667_);
    crate::leanh::lean_dec_ref(v_a_3666_);
    crate::leanh::lean_dec(v_a_3665_);
    crate::leanh::lean_dec_ref(v_a_3664_);
    crate::leanh::lean_dec(v_a_3663_);
    return v_res_3673_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(
    mut v_a_3674_: *mut crate::leanh::LeanObject,
    mut v_as_3675_: *mut crate::leanh::LeanObject,
    mut v_sz_3676_: usize,
    mut v_i_3677_: usize,
    mut v_b_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: usize = 0;
    let mut v___x_3693_: usize = 0;
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3705_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3695_ = lean_usize_dec_lt(v_i_3677_, v_sz_3676_);
                if v___x_3695_ == 0 {
                    crate::leanh::lean_dec(v_a_3674_);
                    v___x_3696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3696_, 0, v_b_3678_);
                    return v___x_3696_;
                } else {
                    v_a_3697_ = lean_array_uget_borrowed(v_as_3675_, v_i_3677_);
                    v___x_3698_ =
                        l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(
                            v_b_3678_, v_a_3697_,
                        );
                    if v___x_3698_ == 0 {
                        v_a_3691_ = v_b_3678_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3674_);
                        crate::leanh::lean_inc(v_a_3697_);
                        v___x_3699_ = l_Lean_Meta_Grind_activateTheorem(
                            v_a_3697_,
                            v_a_3674_,
                            v___y_3679_,
                            v___y_3680_,
                            v___y_3681_,
                            v___y_3682_,
                            v___y_3683_,
                            v___y_3684_,
                            v___y_3685_,
                            v___y_3686_,
                            v___y_3687_,
                            v___y_3688_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3699_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3699_, 1);
                            v_patterns_3700_ = crate::leanh::lean_ctor_get(v_a_3697_, 3);
                            crate::leanh::lean_inc(v_patterns_3700_);
                            v___x_3701_ = lean_array_push(v_b_3678_, v_patterns_3700_);
                            v_a_3691_ = v___x_3701_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_b_3678_);
                            crate::leanh::lean_dec(v_a_3674_);
                            v_a_3702_ = crate::leanh::lean_ctor_get(v___x_3699_, 0);
                            v_isSharedCheck_3709_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3699_)) as u8;
                            if v_isSharedCheck_3709_ == 0 {
                                v___x_3704_ = v___x_3699_;
                                v_isShared_3705_ = v_isSharedCheck_3709_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3702_);
                                crate::leanh::lean_dec(v___x_3699_);
                                v___x_3704_ = crate::leanh::lean_box(0);
                                v_isShared_3705_ = v_isSharedCheck_3709_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3692_ = 1usize;
                v___x_3693_ = lean_usize_add(v_i_3677_, v___x_3692_);
                v_i_3677_ = v___x_3693_;
                v_b_3678_ = v_a_3691_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3705_ == 0 {
                    v___x_3707_ = v___x_3704_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3708_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
                    v___x_3707_ = v_reuseFailAlloc_3708_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_as_3711_: *mut crate::leanh::LeanObject,
    mut v_sz_3712_: *mut crate::leanh::LeanObject,
    mut v_i_3713_: *mut crate::leanh::LeanObject,
    mut v_b_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3726_: usize = 0;
    let mut v_i_boxed_3727_: usize = 0;
    let mut v_res_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3726_ = crate::leanh::lean_unbox_usize(v_sz_3712_);
    crate::leanh::lean_dec(v_sz_3712_);
    v_i_boxed_3727_ = crate::leanh::lean_unbox_usize(v_i_3713_);
    crate::leanh::lean_dec(v_i_3713_);
    v_res_3728_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_3710_, v_as_3711_, v_sz_boxed_3726_, v_i_boxed_3727_, v_b_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
    crate::leanh::lean_dec(v___y_3724_);
    crate::leanh::lean_dec_ref(v___y_3723_);
    crate::leanh::lean_dec(v___y_3722_);
    crate::leanh::lean_dec_ref(v___y_3721_);
    crate::leanh::lean_dec(v___y_3720_);
    crate::leanh::lean_dec_ref(v___y_3719_);
    crate::leanh::lean_dec(v___y_3718_);
    crate::leanh::lean_dec_ref(v___y_3717_);
    crate::leanh::lean_dec(v___y_3716_);
    crate::leanh::lean_dec(v___y_3715_);
    crate::leanh::lean_dec_ref(v_as_3711_);
    return v_res_3728_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3730_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0;
    v___x_3731_ = l_Lean_stringToMessageData(v___x_3730_);
    return v___x_3731_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(
    mut v_e_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
    mut v_a_3744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3755_: u8 = 0;
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3771_: usize = 0;
    let mut v___x_3772_: usize = 0;
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newThms_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3783_: u8 = 0;
    let mut v_size_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v_ematch_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newThms_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v_a_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3830_: u8 = 0;
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut v_unused_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ematch_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newThms_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: u8 = 0;
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3858_: u8 = 0;
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut v_patternsFoundSoFar_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3888_: u8 = 0;
    let mut v_val_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: u8 = 0;
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patterns_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3894_: u8 = 0;
    let mut v_a_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3898_: u8 = 0;
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_a_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v_a_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3914_: u8 = 0;
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_a_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v_a_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3930_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3934_: u8 = 0;
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_a_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3947_: u8 = 0;
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3951_: u8 = 0;
    let mut v_a_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3955_: u8 = 0;
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_3734_);
                v___x_3746_ = l_Lean_Meta_Grind_mkEqTrueProof(
                    v_e_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_,
                    v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_,
                );
                if crate::leanh::lean_obj_tag(v___x_3746_) == 0 {
                    v_a_3747_ = crate::leanh::lean_ctor_get(v___x_3746_, 0);
                    crate::leanh::lean_inc_n(v_a_3747_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_3746_, 1);
                    v___x_3748_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_getOrigin___redArg(v_a_3747_, v_a_3735_, v_a_3742_);
                    if crate::leanh::lean_obj_tag(v___x_3748_) == 0 {
                        v_a_3749_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                        crate::leanh::lean_inc(v_a_3749_);
                        crate::leanh::lean_dec_ref_known(v___x_3748_, 1);
                        crate::leanh::lean_inc_ref(v_e_3734_);
                        v___x_3750_ = l_Lean_Meta_mkOfEqTrueCore(v_e_3734_, v_a_3747_);
                        crate::leanh::lean_inc_ref(v___x_3750_);
                        v___x_3751_ = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(
                            v___x_3750_,
                            v_a_3736_,
                            v_a_3737_,
                            v_a_3738_,
                            v_a_3739_,
                            v_a_3740_,
                            v_a_3741_,
                            v_a_3742_,
                            v_a_3743_,
                            v_a_3744_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3751_) == 0 {
                            v_a_3752_ = crate::leanh::lean_ctor_get(v___x_3751_, 0);
                            v_isSharedCheck_3935_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3751_)) as u8;
                            if v_isSharedCheck_3935_ == 0 {
                                v___x_3754_ = v___x_3751_;
                                v_isShared_3755_ = v_isSharedCheck_3935_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3752_);
                                crate::leanh::lean_dec(v___x_3751_);
                                v___x_3754_ = crate::leanh::lean_box(0);
                                v_isShared_3755_ = v_isSharedCheck_3935_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3750_);
                            crate::leanh::lean_dec(v_a_3749_);
                            crate::leanh::lean_dec_ref(v_e_3734_);
                            v_a_3936_ = crate::leanh::lean_ctor_get(v___x_3751_, 0);
                            v_isSharedCheck_3943_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3751_)) as u8;
                            if v_isSharedCheck_3943_ == 0 {
                                v___x_3938_ = v___x_3751_;
                                v_isShared_3939_ = v_isSharedCheck_3943_;
                                state = 28;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3936_);
                                crate::leanh::lean_dec(v___x_3751_);
                                v___x_3938_ = crate::leanh::lean_box(0);
                                v_isShared_3939_ = v_isSharedCheck_3943_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3747_);
                        crate::leanh::lean_dec_ref(v_e_3734_);
                        v_a_3944_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                        v_isSharedCheck_3951_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3748_)) as u8;
                        if v_isSharedCheck_3951_ == 0 {
                            v___x_3946_ = v___x_3748_;
                            v_isShared_3947_ = v_isSharedCheck_3951_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3944_);
                            crate::leanh::lean_dec(v___x_3748_);
                            v___x_3946_ = crate::leanh::lean_box(0);
                            v_isShared_3947_ = v_isSharedCheck_3951_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3734_);
                    v_a_3952_ = crate::leanh::lean_ctor_get(v___x_3746_, 0);
                    v_isSharedCheck_3959_ = (!crate::leanh::lean_is_exclusive(v___x_3746_)) as u8;
                    if v_isSharedCheck_3959_ == 0 {
                        v___x_3954_ = v___x_3746_;
                        v_isShared_3955_ = v_isSharedCheck_3959_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3952_);
                        crate::leanh::lean_dec(v___x_3746_);
                        v___x_3954_ = crate::leanh::lean_box(0);
                        v_isShared_3955_ = v_isSharedCheck_3959_;
                        state = 32;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3756_ = (crate::leanh::lean_unbox(v_a_3752_) as u8);
                crate::leanh::lean_dec(v_a_3752_);
                if v___x_3756_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3750_);
                    crate::leanh::lean_dec(v_a_3749_);
                    crate::leanh::lean_dec_ref(v_e_3734_);
                    v___x_3757_ = crate::leanh::lean_box(0);
                    if v_isShared_3755_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3754_, 0, v___x_3757_);
                        v___x_3759_ = v___x_3754_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3760_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
                        v___x_3759_ = v_reuseFailAlloc_3760_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3754_);
                    v___x_3761_ = lean_st_ref_get(v_a_3735_);
                    v___x_3762_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3734_, v_a_3735_);
                    if crate::leanh::lean_obj_tag(v___x_3762_) == 0 {
                        v_a_3763_ = crate::leanh::lean_ctor_get(v___x_3762_, 0);
                        crate::leanh::lean_inc(v_a_3763_);
                        crate::leanh::lean_dec_ref_known(v___x_3762_, 1);
                        v___x_3764_ = l_Lean_Meta_Grind_getSymbolPriorities___redArg(v_a_3737_);
                        if crate::leanh::lean_obj_tag(v___x_3764_) == 0 {
                            v_a_3765_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
                            crate::leanh::lean_inc_n(v_a_3765_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_3764_, 1);
                            v___x_3766_ = crate::leanh::lean_unsigned_to_nat(1000);
                            v___x_3767_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
                            v___x_3768_ = 0;
                            crate::leanh::lean_inc_ref(v___x_3750_);
                            crate::leanh::lean_inc(v_a_3749_);
                            v___x_3769_ = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(
                                v_a_3749_,
                                v___x_3767_,
                                v___x_3750_,
                                v___x_3766_,
                                v_a_3765_,
                                v___x_3768_,
                                v_a_3741_,
                                v_a_3742_,
                                v_a_3743_,
                                v_a_3744_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3769_) == 0 {
                                v_a_3770_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                                crate::leanh::lean_inc(v_a_3770_);
                                crate::leanh::lean_dec_ref_known(v___x_3769_, 1);
                                v_sz_3771_ = lean_array_size(v_a_3770_);
                                v___x_3772_ = 0usize;
                                crate::leanh::lean_inc(v_a_3763_);
                                v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(v_a_3763_, v_a_3770_, v_sz_3771_, v___x_3772_, v___x_3767_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_);
                                crate::leanh::lean_dec(v_a_3770_);
                                if crate::leanh::lean_obj_tag(v___x_3773_) == 0 {
                                    v_a_3774_ = crate::leanh::lean_ctor_get(v___x_3773_, 0);
                                    crate::leanh::lean_inc(v_a_3774_);
                                    crate::leanh::lean_dec_ref_known(v___x_3773_, 1);
                                    v___x_3775_ = crate::leanh::lean_box(6);
                                    crate::leanh::lean_inc(v_a_3765_);
                                    crate::leanh::lean_inc_ref(v___x_3750_);
                                    crate::leanh::lean_inc(v_a_3749_);
                                    v___x_3776_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_3749_, v___x_3750_, v___x_3775_, v_a_3765_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_);
                                    if crate::leanh::lean_obj_tag(v___x_3776_) == 0 {
                                        v_toGoalState_3777_ =
                                            crate::leanh::lean_ctor_get(v___x_3761_, 0);
                                        crate::leanh::lean_inc_ref(v_toGoalState_3777_);
                                        crate::leanh::lean_dec(v___x_3761_);
                                        v_ematch_3778_ =
                                            crate::leanh::lean_ctor_get(v_toGoalState_3777_, 12);
                                        crate::leanh::lean_inc_ref(v_ematch_3778_);
                                        crate::leanh::lean_dec_ref(v_toGoalState_3777_);
                                        v_newThms_3779_ =
                                            crate::leanh::lean_ctor_get(v_ematch_3778_, 3);
                                        crate::leanh::lean_inc_ref(v_newThms_3779_);
                                        crate::leanh::lean_dec_ref(v_ematch_3778_);
                                        v_a_3780_ = crate::leanh::lean_ctor_get(v___x_3776_, 0);
                                        v_isSharedCheck_3894_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3776_)) as u8;
                                        if v_isSharedCheck_3894_ == 0 {
                                            v___x_3782_ = v___x_3776_;
                                            v_isShared_3783_ = v_isSharedCheck_3894_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3780_);
                                            crate::leanh::lean_dec(v___x_3776_);
                                            v___x_3782_ = crate::leanh::lean_box(0);
                                            v_isShared_3783_ = v_isSharedCheck_3894_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_3774_);
                                        crate::leanh::lean_dec(v_a_3765_);
                                        crate::leanh::lean_dec(v_a_3763_);
                                        crate::leanh::lean_dec(v___x_3761_);
                                        crate::leanh::lean_dec_ref(v___x_3750_);
                                        crate::leanh::lean_dec(v_a_3749_);
                                        crate::leanh::lean_dec_ref(v_e_3734_);
                                        v_a_3895_ = crate::leanh::lean_ctor_get(v___x_3776_, 0);
                                        v_isSharedCheck_3902_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3776_)) as u8;
                                        if v_isSharedCheck_3902_ == 0 {
                                            v___x_3897_ = v___x_3776_;
                                            v_isShared_3898_ = v_isSharedCheck_3902_;
                                            state = 18;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3895_);
                                            crate::leanh::lean_dec(v___x_3776_);
                                            v___x_3897_ = crate::leanh::lean_box(0);
                                            v_isShared_3898_ = v_isSharedCheck_3902_;
                                            state = 18;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_3765_);
                                    crate::leanh::lean_dec(v_a_3763_);
                                    crate::leanh::lean_dec(v___x_3761_);
                                    crate::leanh::lean_dec_ref(v___x_3750_);
                                    crate::leanh::lean_dec(v_a_3749_);
                                    crate::leanh::lean_dec_ref(v_e_3734_);
                                    v_a_3903_ = crate::leanh::lean_ctor_get(v___x_3773_, 0);
                                    v_isSharedCheck_3910_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3773_)) as u8;
                                    if v_isSharedCheck_3910_ == 0 {
                                        v___x_3905_ = v___x_3773_;
                                        v_isShared_3906_ = v_isSharedCheck_3910_;
                                        state = 20;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3903_);
                                        crate::leanh::lean_dec(v___x_3773_);
                                        v___x_3905_ = crate::leanh::lean_box(0);
                                        v_isShared_3906_ = v_isSharedCheck_3910_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3765_);
                                crate::leanh::lean_dec(v_a_3763_);
                                crate::leanh::lean_dec(v___x_3761_);
                                crate::leanh::lean_dec_ref(v___x_3750_);
                                crate::leanh::lean_dec(v_a_3749_);
                                crate::leanh::lean_dec_ref(v_e_3734_);
                                v_a_3911_ = crate::leanh::lean_ctor_get(v___x_3769_, 0);
                                v_isSharedCheck_3918_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3769_)) as u8;
                                if v_isSharedCheck_3918_ == 0 {
                                    v___x_3913_ = v___x_3769_;
                                    v_isShared_3914_ = v_isSharedCheck_3918_;
                                    state = 22;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3911_);
                                    crate::leanh::lean_dec(v___x_3769_);
                                    v___x_3913_ = crate::leanh::lean_box(0);
                                    v_isShared_3914_ = v_isSharedCheck_3918_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3763_);
                            crate::leanh::lean_dec(v___x_3761_);
                            crate::leanh::lean_dec_ref(v___x_3750_);
                            crate::leanh::lean_dec(v_a_3749_);
                            crate::leanh::lean_dec_ref(v_e_3734_);
                            v_a_3919_ = crate::leanh::lean_ctor_get(v___x_3764_, 0);
                            v_isSharedCheck_3926_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3764_)) as u8;
                            if v_isSharedCheck_3926_ == 0 {
                                v___x_3921_ = v___x_3764_;
                                v_isShared_3922_ = v_isSharedCheck_3926_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3919_);
                                crate::leanh::lean_dec(v___x_3764_);
                                v___x_3921_ = crate::leanh::lean_box(0);
                                v_isShared_3922_ = v_isSharedCheck_3926_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3761_);
                        crate::leanh::lean_dec_ref(v___x_3750_);
                        crate::leanh::lean_dec(v_a_3749_);
                        crate::leanh::lean_dec_ref(v_e_3734_);
                        v_a_3927_ = crate::leanh::lean_ctor_get(v___x_3762_, 0);
                        v_isSharedCheck_3934_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3762_)) as u8;
                        if v_isSharedCheck_3934_ == 0 {
                            v___x_3929_ = v___x_3762_;
                            v_isShared_3930_ = v_isSharedCheck_3934_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3927_);
                            crate::leanh::lean_dec(v___x_3762_);
                            v___x_3929_ = crate::leanh::lean_box(0);
                            v_isShared_3930_ = v_isSharedCheck_3934_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3759_;
            }
            3 => {
                v_size_3784_ = crate::leanh::lean_ctor_get(v_newThms_3779_, 2);
                crate::leanh::lean_inc(v_size_3784_);
                crate::leanh::lean_dec_ref(v_newThms_3779_);
                if crate::leanh::lean_obj_tag(v_a_3780_) == 1 {
                    v_val_3889_ = crate::leanh::lean_ctor_get(v_a_3780_, 0);
                    crate::leanh::lean_inc(v_val_3889_);
                    crate::leanh::lean_dec_ref_known(v_a_3780_, 1);
                    v___x_3890_ =
                        l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(
                            v_a_3774_,
                            v_val_3889_,
                        );
                    if v___x_3890_ == 0 {
                        crate::leanh::lean_dec(v_val_3889_);
                        v_patternsFoundSoFar_3864_ = v_a_3774_;
                        v___y_3865_ = v_a_3735_;
                        v___y_3866_ = v_a_3736_;
                        v___y_3867_ = v_a_3737_;
                        v___y_3868_ = v_a_3738_;
                        v___y_3869_ = v_a_3739_;
                        v___y_3870_ = v_a_3740_;
                        v___y_3871_ = v_a_3741_;
                        v___y_3872_ = v_a_3742_;
                        v___y_3873_ = v_a_3743_;
                        v___y_3874_ = v_a_3744_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3763_);
                        crate::leanh::lean_inc(v_val_3889_);
                        v___x_3891_ = l_Lean_Meta_Grind_activateTheorem(
                            v_val_3889_,
                            v_a_3763_,
                            v_a_3735_,
                            v_a_3736_,
                            v_a_3737_,
                            v_a_3738_,
                            v_a_3739_,
                            v_a_3740_,
                            v_a_3741_,
                            v_a_3742_,
                            v_a_3743_,
                            v_a_3744_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3891_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3891_, 1);
                            v_patterns_3892_ = crate::leanh::lean_ctor_get(v_val_3889_, 3);
                            crate::leanh::lean_inc(v_patterns_3892_);
                            crate::leanh::lean_dec(v_val_3889_);
                            v___x_3893_ = lean_array_push(v_a_3774_, v_patterns_3892_);
                            v_patternsFoundSoFar_3864_ = v___x_3893_;
                            v___y_3865_ = v_a_3735_;
                            v___y_3866_ = v_a_3736_;
                            v___y_3867_ = v_a_3737_;
                            v___y_3868_ = v_a_3738_;
                            v___y_3869_ = v_a_3739_;
                            v___y_3870_ = v_a_3740_;
                            v___y_3871_ = v_a_3741_;
                            v___y_3872_ = v_a_3742_;
                            v___y_3873_ = v_a_3743_;
                            v___y_3874_ = v_a_3744_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_val_3889_);
                            crate::leanh::lean_dec(v_size_3784_);
                            crate::leanh::lean_del_object(v___x_3782_);
                            crate::leanh::lean_dec(v_a_3774_);
                            crate::leanh::lean_dec(v_a_3765_);
                            crate::leanh::lean_dec(v_a_3763_);
                            crate::leanh::lean_dec_ref(v___x_3750_);
                            crate::leanh::lean_dec(v_a_3749_);
                            crate::leanh::lean_dec_ref(v_e_3734_);
                            return v___x_3891_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3780_);
                    v_patternsFoundSoFar_3864_ = v_a_3774_;
                    v___y_3865_ = v_a_3735_;
                    v___y_3866_ = v_a_3736_;
                    v___y_3867_ = v_a_3737_;
                    v___y_3868_ = v_a_3738_;
                    v___y_3869_ = v_a_3739_;
                    v___y_3870_ = v_a_3740_;
                    v___y_3871_ = v_a_3741_;
                    v___y_3872_ = v_a_3742_;
                    v___y_3873_ = v_a_3743_;
                    v___y_3874_ = v_a_3744_;
                    state = 15;
                    continue;
                }
            }
            4 => {
                v___x_3793_ = lean_st_ref_get(v___y_3786_);
                v_toGoalState_3794_ = crate::leanh::lean_ctor_get(v___x_3793_, 0);
                v_isSharedCheck_3831_ = (!crate::leanh::lean_is_exclusive(v___x_3793_)) as u8;
                if v_isSharedCheck_3831_ == 0 {
                    v_unused_3832_ = crate::leanh::lean_ctor_get(v___x_3793_, 1);
                    crate::leanh::lean_dec(v_unused_3832_);
                    v___x_3796_ = v___x_3793_;
                    v_isShared_3797_ = v_isSharedCheck_3831_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toGoalState_3794_);
                    crate::leanh::lean_dec(v___x_3793_);
                    v___x_3796_ = crate::leanh::lean_box(0);
                    v_isShared_3797_ = v_isSharedCheck_3831_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_ematch_3798_ = crate::leanh::lean_ctor_get(v_toGoalState_3794_, 12);
                crate::leanh::lean_inc_ref(v_ematch_3798_);
                crate::leanh::lean_dec_ref(v_toGoalState_3794_);
                v_newThms_3799_ = crate::leanh::lean_ctor_get(v_ematch_3798_, 3);
                crate::leanh::lean_inc_ref(v_newThms_3799_);
                crate::leanh::lean_dec_ref(v_ematch_3798_);
                v_size_3800_ = crate::leanh::lean_ctor_get(v_newThms_3799_, 2);
                crate::leanh::lean_inc(v_size_3800_);
                crate::leanh::lean_dec_ref(v_newThms_3799_);
                v___x_3801_ = lean_nat_dec_eq(v_size_3800_, v_size_3784_);
                crate::leanh::lean_dec(v_size_3784_);
                crate::leanh::lean_dec(v_size_3800_);
                if v___x_3801_ == 0 {
                    crate::leanh::lean_del_object(v___x_3796_);
                    crate::leanh::lean_dec_ref(v_e_3734_);
                    v___x_3802_ = crate::leanh::lean_box(0);
                    if v_isShared_3783_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3782_, 0, v___x_3802_);
                        v___x_3804_ = v___x_3782_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3805_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3805_, 0, v___x_3802_);
                        v___x_3804_ = v_reuseFailAlloc_3805_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3782_);
                    v___x_3806_ = l_Lean_Meta_Sym_getConfig___redArg(v___y_3787_);
                    if crate::leanh::lean_obj_tag(v___x_3806_) == 0 {
                        v_a_3807_ = crate::leanh::lean_ctor_get(v___x_3806_, 0);
                        v_isSharedCheck_3822_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3806_)) as u8;
                        if v_isSharedCheck_3822_ == 0 {
                            v___x_3809_ = v___x_3806_;
                            v_isShared_3810_ = v_isSharedCheck_3822_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3807_);
                            crate::leanh::lean_dec(v___x_3806_);
                            v___x_3809_ = crate::leanh::lean_box(0);
                            v_isShared_3810_ = v_isSharedCheck_3822_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3796_);
                        crate::leanh::lean_dec_ref(v_e_3734_);
                        v_a_3823_ = crate::leanh::lean_ctor_get(v___x_3806_, 0);
                        v_isSharedCheck_3830_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3806_)) as u8;
                        if v_isSharedCheck_3830_ == 0 {
                            v___x_3825_ = v___x_3806_;
                            v_isShared_3826_ = v_isSharedCheck_3830_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3823_);
                            crate::leanh::lean_dec(v___x_3806_);
                            v___x_3825_ = crate::leanh::lean_box(0);
                            v_isShared_3826_ = v_isSharedCheck_3830_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_3804_;
            }
            7 => {
                v___x_3811_ = (crate::leanh::lean_unbox(v_a_3807_) as u8);
                crate::leanh::lean_dec(v_a_3807_);
                if v___x_3811_ == 0 {
                    crate::leanh::lean_del_object(v___x_3796_);
                    crate::leanh::lean_dec_ref(v_e_3734_);
                    v___x_3812_ = crate::leanh::lean_box(0);
                    if v_isShared_3810_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3809_, 0, v___x_3812_);
                        v___x_3814_ = v___x_3809_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
                        v___x_3814_ = v_reuseFailAlloc_3815_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3809_);
                    v___x_3816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
                    v___x_3817_ = l_Lean_indentExpr(v_e_3734_);
                    if v_isShared_3797_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3796_, 7);
                        crate::leanh::lean_ctor_set(v___x_3796_, 1, v___x_3817_);
                        crate::leanh::lean_ctor_set(v___x_3796_, 0, v___x_3816_);
                        v___x_3819_ = v___x_3796_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3821_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3816_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 1, v___x_3817_);
                        v___x_3819_ = v_reuseFailAlloc_3821_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_3814_;
            }
            9 => {
                v___x_3820_ = l_Lean_Meta_Sym_reportIssue(
                    v___x_3819_,
                    v___y_3787_,
                    v___y_3788_,
                    v___y_3789_,
                    v___y_3790_,
                    v___y_3791_,
                    v___y_3792_,
                );
                return v___x_3820_;
            }
            10 => {
                if v_isShared_3826_ == 0 {
                    v___x_3828_ = v___x_3825_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
                    v___x_3828_ = v_reuseFailAlloc_3829_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3828_;
            }
            12 => {
                v___x_3844_ = lean_st_ref_get(v___y_3834_);
                v_toGoalState_3845_ = crate::leanh::lean_ctor_get(v___x_3844_, 0);
                crate::leanh::lean_inc_ref(v_toGoalState_3845_);
                crate::leanh::lean_dec(v___x_3844_);
                v_ematch_3846_ = crate::leanh::lean_ctor_get(v_toGoalState_3845_, 12);
                crate::leanh::lean_inc_ref(v_ematch_3846_);
                crate::leanh::lean_dec_ref(v_toGoalState_3845_);
                v_newThms_3847_ = crate::leanh::lean_ctor_get(v_ematch_3846_, 3);
                crate::leanh::lean_inc_ref(v_newThms_3847_);
                crate::leanh::lean_dec_ref(v_ematch_3846_);
                v_size_3848_ = crate::leanh::lean_ctor_get(v_newThms_3847_, 2);
                crate::leanh::lean_inc(v_size_3848_);
                crate::leanh::lean_dec_ref(v_newThms_3847_);
                v___x_3849_ = lean_nat_dec_eq(v_size_3848_, v_size_3784_);
                crate::leanh::lean_dec(v_size_3848_);
                if v___x_3849_ == 0 {
                    crate::leanh::lean_dec(v_a_3765_);
                    crate::leanh::lean_dec(v_a_3763_);
                    crate::leanh::lean_dec_ref(v___x_3750_);
                    crate::leanh::lean_dec(v_a_3749_);
                    v___y_3786_ = v___y_3834_;
                    v___y_3787_ = v___y_3838_;
                    v___y_3788_ = v___y_3839_;
                    v___y_3789_ = v___y_3840_;
                    v___y_3790_ = v___y_3841_;
                    v___y_3791_ = v___y_3842_;
                    v___y_3792_ = v___y_3843_;
                    state = 4;
                    continue;
                } else {
                    v___x_3850_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2;
                    v___x_3851_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_3749_, v___x_3750_, v___x_3850_, v_a_3765_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
                    if crate::leanh::lean_obj_tag(v___x_3851_) == 0 {
                        v_a_3852_ = crate::leanh::lean_ctor_get(v___x_3851_, 0);
                        crate::leanh::lean_inc(v_a_3852_);
                        crate::leanh::lean_dec_ref_known(v___x_3851_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3852_) == 1 {
                            v_val_3853_ = crate::leanh::lean_ctor_get(v_a_3852_, 0);
                            crate::leanh::lean_inc(v_val_3853_);
                            crate::leanh::lean_dec_ref_known(v_a_3852_, 1);
                            v___x_3854_ = l_Lean_Meta_Grind_activateTheorem(
                                v_val_3853_,
                                v_a_3763_,
                                v___y_3834_,
                                v___y_3835_,
                                v___y_3836_,
                                v___y_3837_,
                                v___y_3838_,
                                v___y_3839_,
                                v___y_3840_,
                                v___y_3841_,
                                v___y_3842_,
                                v___y_3843_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3854_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3854_, 1);
                                v___y_3786_ = v___y_3834_;
                                v___y_3787_ = v___y_3838_;
                                v___y_3788_ = v___y_3839_;
                                v___y_3789_ = v___y_3840_;
                                v___y_3790_ = v___y_3841_;
                                v___y_3791_ = v___y_3842_;
                                v___y_3792_ = v___y_3843_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_size_3784_);
                                crate::leanh::lean_del_object(v___x_3782_);
                                crate::leanh::lean_dec_ref(v_e_3734_);
                                return v___x_3854_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3852_);
                            crate::leanh::lean_dec(v_a_3763_);
                            v___y_3786_ = v___y_3834_;
                            v___y_3787_ = v___y_3838_;
                            v___y_3788_ = v___y_3839_;
                            v___y_3789_ = v___y_3840_;
                            v___y_3790_ = v___y_3841_;
                            v___y_3791_ = v___y_3842_;
                            v___y_3792_ = v___y_3843_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_3784_);
                        crate::leanh::lean_del_object(v___x_3782_);
                        crate::leanh::lean_dec(v_a_3763_);
                        crate::leanh::lean_dec_ref(v_e_3734_);
                        v_a_3855_ = crate::leanh::lean_ctor_get(v___x_3851_, 0);
                        v_isSharedCheck_3862_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3851_)) as u8;
                        if v_isSharedCheck_3862_ == 0 {
                            v___x_3857_ = v___x_3851_;
                            v_isShared_3858_ = v_isSharedCheck_3862_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3855_);
                            crate::leanh::lean_dec(v___x_3851_);
                            v___x_3857_ = crate::leanh::lean_box(0);
                            v_isShared_3858_ = v_isSharedCheck_3862_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            13 => {
                if v_isShared_3858_ == 0 {
                    v___x_3860_ = v___x_3857_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
                    v___x_3860_ = v_reuseFailAlloc_3861_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3860_;
            }
            15 => {
                v___x_3875_ = crate::leanh::lean_box(7);
                crate::leanh::lean_inc(v_a_3765_);
                crate::leanh::lean_inc_ref(v___x_3750_);
                crate::leanh::lean_inc(v_a_3749_);
                v___x_3876_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(v_a_3749_, v___x_3750_, v___x_3875_, v_a_3765_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
                if crate::leanh::lean_obj_tag(v___x_3876_) == 0 {
                    v_a_3877_ = crate::leanh::lean_ctor_get(v___x_3876_, 0);
                    crate::leanh::lean_inc(v_a_3877_);
                    crate::leanh::lean_dec_ref_known(v___x_3876_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3877_) == 1 {
                        v_val_3878_ = crate::leanh::lean_ctor_get(v_a_3877_, 0);
                        crate::leanh::lean_inc(v_val_3878_);
                        crate::leanh::lean_dec_ref_known(v_a_3877_, 1);
                        v___x_3879_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(v_patternsFoundSoFar_3864_, v_val_3878_);
                        crate::leanh::lean_dec_ref(v_patternsFoundSoFar_3864_);
                        if v___x_3879_ == 0 {
                            crate::leanh::lean_dec(v_val_3878_);
                            v___y_3834_ = v___y_3865_;
                            v___y_3835_ = v___y_3866_;
                            v___y_3836_ = v___y_3867_;
                            v___y_3837_ = v___y_3868_;
                            v___y_3838_ = v___y_3869_;
                            v___y_3839_ = v___y_3870_;
                            v___y_3840_ = v___y_3871_;
                            v___y_3841_ = v___y_3872_;
                            v___y_3842_ = v___y_3873_;
                            v___y_3843_ = v___y_3874_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3763_);
                            v___x_3880_ = l_Lean_Meta_Grind_activateTheorem(
                                v_val_3878_,
                                v_a_3763_,
                                v___y_3865_,
                                v___y_3866_,
                                v___y_3867_,
                                v___y_3868_,
                                v___y_3869_,
                                v___y_3870_,
                                v___y_3871_,
                                v___y_3872_,
                                v___y_3873_,
                                v___y_3874_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3880_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3880_, 1);
                                v___y_3834_ = v___y_3865_;
                                v___y_3835_ = v___y_3866_;
                                v___y_3836_ = v___y_3867_;
                                v___y_3837_ = v___y_3868_;
                                v___y_3838_ = v___y_3869_;
                                v___y_3839_ = v___y_3870_;
                                v___y_3840_ = v___y_3871_;
                                v___y_3841_ = v___y_3872_;
                                v___y_3842_ = v___y_3873_;
                                v___y_3843_ = v___y_3874_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_size_3784_);
                                crate::leanh::lean_del_object(v___x_3782_);
                                crate::leanh::lean_dec(v_a_3765_);
                                crate::leanh::lean_dec(v_a_3763_);
                                crate::leanh::lean_dec_ref(v___x_3750_);
                                crate::leanh::lean_dec(v_a_3749_);
                                crate::leanh::lean_dec_ref(v_e_3734_);
                                return v___x_3880_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3877_);
                        crate::leanh::lean_dec_ref(v_patternsFoundSoFar_3864_);
                        v___y_3834_ = v___y_3865_;
                        v___y_3835_ = v___y_3866_;
                        v___y_3836_ = v___y_3867_;
                        v___y_3837_ = v___y_3868_;
                        v___y_3838_ = v___y_3869_;
                        v___y_3839_ = v___y_3870_;
                        v___y_3840_ = v___y_3871_;
                        v___y_3841_ = v___y_3872_;
                        v___y_3842_ = v___y_3873_;
                        v___y_3843_ = v___y_3874_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_patternsFoundSoFar_3864_);
                    crate::leanh::lean_dec(v_size_3784_);
                    crate::leanh::lean_del_object(v___x_3782_);
                    crate::leanh::lean_dec(v_a_3765_);
                    crate::leanh::lean_dec(v_a_3763_);
                    crate::leanh::lean_dec_ref(v___x_3750_);
                    crate::leanh::lean_dec(v_a_3749_);
                    crate::leanh::lean_dec_ref(v_e_3734_);
                    v_a_3881_ = crate::leanh::lean_ctor_get(v___x_3876_, 0);
                    v_isSharedCheck_3888_ = (!crate::leanh::lean_is_exclusive(v___x_3876_)) as u8;
                    if v_isSharedCheck_3888_ == 0 {
                        v___x_3883_ = v___x_3876_;
                        v_isShared_3884_ = v_isSharedCheck_3888_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3881_);
                        crate::leanh::lean_dec(v___x_3876_);
                        v___x_3883_ = crate::leanh::lean_box(0);
                        v_isShared_3884_ = v_isSharedCheck_3888_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_3884_ == 0 {
                    v___x_3886_ = v___x_3883_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
                    v___x_3886_ = v_reuseFailAlloc_3887_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3886_;
            }
            18 => {
                if v_isShared_3898_ == 0 {
                    v___x_3900_ = v___x_3897_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
                    v___x_3900_ = v_reuseFailAlloc_3901_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3900_;
            }
            20 => {
                if v_isShared_3906_ == 0 {
                    v___x_3908_ = v___x_3905_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3909_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3908_;
            }
            22 => {
                if v_isShared_3914_ == 0 {
                    v___x_3916_ = v___x_3913_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
                    v___x_3916_ = v_reuseFailAlloc_3917_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3916_;
            }
            24 => {
                if v_isShared_3922_ == 0 {
                    v___x_3924_ = v___x_3921_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3924_;
            }
            26 => {
                if v_isShared_3930_ == 0 {
                    v___x_3932_ = v___x_3929_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3933_, 0, v_a_3927_);
                    v___x_3932_ = v_reuseFailAlloc_3933_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3932_;
            }
            28 => {
                if v_isShared_3939_ == 0 {
                    v___x_3941_ = v___x_3938_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3941_;
            }
            30 => {
                if v_isShared_3947_ == 0 {
                    v___x_3949_ = v___x_3946_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3950_, 0, v_a_3944_);
                    v___x_3949_ = v_reuseFailAlloc_3950_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3949_;
            }
            32 => {
                if v_isShared_3955_ == 0 {
                    v___x_3957_ = v___x_3954_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
                    v___x_3957_ = v_reuseFailAlloc_3958_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(
    mut v_e_3960_: *mut crate::leanh::LeanObject,
    mut v_a_3961_: *mut crate::leanh::LeanObject,
    mut v_a_3962_: *mut crate::leanh::LeanObject,
    mut v_a_3963_: *mut crate::leanh::LeanObject,
    mut v_a_3964_: *mut crate::leanh::LeanObject,
    mut v_a_3965_: *mut crate::leanh::LeanObject,
    mut v_a_3966_: *mut crate::leanh::LeanObject,
    mut v_a_3967_: *mut crate::leanh::LeanObject,
    mut v_a_3968_: *mut crate::leanh::LeanObject,
    mut v_a_3969_: *mut crate::leanh::LeanObject,
    mut v_a_3970_: *mut crate::leanh::LeanObject,
    mut v_a_3971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3972_ =
        l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(
            v_e_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_, v_a_3967_,
            v_a_3968_, v_a_3969_, v_a_3970_,
        );
    crate::leanh::lean_dec(v_a_3970_);
    crate::leanh::lean_dec_ref(v_a_3969_);
    crate::leanh::lean_dec(v_a_3968_);
    crate::leanh::lean_dec_ref(v_a_3967_);
    crate::leanh::lean_dec(v_a_3966_);
    crate::leanh::lean_dec_ref(v_a_3965_);
    crate::leanh::lean_dec(v_a_3964_);
    crate::leanh::lean_dec_ref(v_a_3963_);
    crate::leanh::lean_dec(v_a_3962_);
    crate::leanh::lean_dec(v_a_3961_);
    return v_res_3972_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3977_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
    v___x_3978_ = l_Lean_Meta_Grind_propagateForallPropUp___lam__0___closed__1;
    v___x_3979_ = l_Lean_Name_append(v___x_3978_, v___x_3977_);
    return v___x_3979_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
    v___x_3982_ = l_Lean_stringToMessageData(v___x_3981_);
    return v___x_3982_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ = crate::leanh::lean_box(0);
    v___x_3997_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
    v___x_3998_ = l_Lean_mkConst(v___x_3997_, v___x_3996_);
    return v___x_3998_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4004_ = crate::leanh::lean_box(0);
    v___x_4005_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
    v___x_4006_ = l_Lean_mkConst(v___x_4005_, v___x_4004_);
    return v___x_4006_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateForallPropDown(
    mut v_e_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
    mut v_a_4011_: *mut crate::leanh::LeanObject,
    mut v_a_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
    mut v_a_4014_: *mut crate::leanh::LeanObject,
    mut v_a_4015_: *mut crate::leanh::LeanObject,
    mut v_a_4016_: *mut crate::leanh::LeanObject,
    mut v_a_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_binderName_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4022_: u8 = 0;
    let mut v___y_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4038_: u8 = 0;
    let mut v___x_4039_: u8 = 0;
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4054_: u8 = 0;
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4058_: u8 = 0;
    let mut v_a_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_a_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4071_: u8 = 0;
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4075_: u8 = 0;
    let mut v___y_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4093_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4102_: u8 = 0;
    let mut v_a_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4115_: u8 = 0;
    let mut v___x_4116_: u8 = 0;
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4122_: u8 = 0;
    let mut v_a_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4126_: u8 = 0;
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4130_: u8 = 0;
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: u8 = 0;
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4138_: u8 = 0;
    let mut v___x_4139_: u8 = 0;
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4149_: u8 = 0;
    let mut v_fst_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4154_: u8 = 0;
    let mut v___y_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_a_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4188_: u8 = 0;
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v_options_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4194_: u8 = 0;
    let mut v_inheritedTraceOptions_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: u8 = 0;
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4208_: u8 = 0;
    let mut v_isSharedCheck_4209_: u8 = 0;
    let mut v_a_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4213_: u8 = 0;
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4217_: u8 = 0;
    let mut v_isSharedCheck_4218_: u8 = 0;
    let mut v_a_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4222_: u8 = 0;
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4226_: u8 = 0;
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4253_: u8 = 0;
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut v_a_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4261_: u8 = 0;
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut v_a_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4269_: u8 = 0;
    let mut v___x_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4273_: u8 = 0;
    let mut v___x_4274_: u8 = 0;
    let mut v___x_4275_: u8 = 0;
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v_a_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4295_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4299_: u8 = 0;
    let mut v_a_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4303_: u8 = 0;
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4307_: u8 = 0;
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_4007_) == 7 {
                    v_binderName_4019_ = crate::leanh::lean_ctor_get(v_e_4007_, 0);
                    v_binderType_4020_ = crate::leanh::lean_ctor_get(v_e_4007_, 1);
                    v_body_4021_ = crate::leanh::lean_ctor_get(v_e_4007_, 2);
                    v_binderInfo_4022_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_4007_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_inc_ref(v_e_4007_);
                    v___x_4131_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                        v_e_4007_, v_a_4008_, v_a_4012_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4131_) == 0 {
                        v_a_4132_ = crate::leanh::lean_ctor_get(v___x_4131_, 0);
                        crate::leanh::lean_inc(v_a_4132_);
                        crate::leanh::lean_dec_ref_known(v___x_4131_, 1);
                        v___x_4133_ = (crate::leanh::lean_unbox(v_a_4132_) as u8);
                        crate::leanh::lean_dec(v_a_4132_);
                        if v___x_4133_ == 0 {
                            crate::leanh::lean_inc_ref(v_e_4007_);
                            v___x_4134_ = l_Lean_Meta_Grind_isEqTrue___redArg(
                                v_e_4007_, v_a_4008_, v_a_4012_, v_a_4014_, v_a_4015_, v_a_4016_,
                                v_a_4017_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4134_) == 0 {
                                v_a_4135_ = crate::leanh::lean_ctor_get(v___x_4134_, 0);
                                v_isSharedCheck_4218_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4134_)) as u8;
                                if v_isSharedCheck_4218_ == 0 {
                                    v___x_4137_ = v___x_4134_;
                                    v_isShared_4138_ = v_isSharedCheck_4218_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4135_);
                                    crate::leanh::lean_dec(v___x_4134_);
                                    v___x_4137_ = crate::leanh::lean_box(0);
                                    v_isShared_4138_ = v_isSharedCheck_4218_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                                v_a_4219_ = crate::leanh::lean_ctor_get(v___x_4134_, 0);
                                v_isSharedCheck_4226_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4134_)) as u8;
                                if v_isSharedCheck_4226_ == 0 {
                                    v___x_4221_ = v___x_4134_;
                                    v_isShared_4222_ = v_isSharedCheck_4226_;
                                    state = 32;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4219_);
                                    crate::leanh::lean_dec(v___x_4134_);
                                    v___x_4221_ = crate::leanh::lean_box(0);
                                    v_isShared_4222_ = v_isSharedCheck_4226_;
                                    state = 32;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_binderType_4020_);
                            v___x_4227_ = l_Lean_Meta_isProp(
                                v_binderType_4020_,
                                v_a_4014_,
                                v_a_4015_,
                                v_a_4016_,
                                v_a_4017_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4227_) == 0 {
                                v_a_4228_ = crate::leanh::lean_ctor_get(v___x_4227_, 0);
                                crate::leanh::lean_inc(v_a_4228_);
                                crate::leanh::lean_dec_ref_known(v___x_4227_, 1);
                                v___x_4274_ = l_Lean_Expr_hasLooseBVars(v_body_4021_);
                                if v___x_4274_ == 0 {
                                    v___x_4275_ = (crate::leanh::lean_unbox(v_a_4228_) as u8);
                                    crate::leanh::lean_dec(v_a_4228_);
                                    if v___x_4275_ == 0 {
                                        state = 34;
                                        continue;
                                    } else {
                                        if v___x_4274_ == 0 {
                                            crate::leanh::lean_inc_ref(v_body_4021_);
                                            crate::leanh::lean_inc_ref(v_binderType_4020_);
                                            v___x_4276_ = l_Lean_Meta_Grind_mkEqFalseProof(
                                                v_e_4007_, v_a_4008_, v_a_4009_, v_a_4010_,
                                                v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_,
                                                v_a_4015_, v_a_4016_, v_a_4017_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_4276_) == 0 {
                                                v_a_4277_ =
                                                    crate::leanh::lean_ctor_get(v___x_4276_, 0);
                                                crate::leanh::lean_inc_n(v_a_4277_, 2);
                                                crate::leanh::lean_dec_ref_known(v___x_4276_, 1);
                                                v___x_4278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropDown___closed__11), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropDown___closed__11_once), _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
                                                crate::leanh::lean_inc_ref(v_body_4021_);
                                                crate::leanh::lean_inc_ref_n(v_binderType_4020_, 2);
                                                v___x_4279_ = l_Lean_mkApp3(
                                                    v___x_4278_,
                                                    v_binderType_4020_,
                                                    v_body_4021_,
                                                    v_a_4277_,
                                                );
                                                v___x_4280_ = l_Lean_Meta_Grind_pushEqTrue___redArg(
                                                    v_binderType_4020_,
                                                    v___x_4279_,
                                                    v_a_4008_,
                                                    v_a_4010_,
                                                    v_a_4012_,
                                                    v_a_4014_,
                                                    v_a_4015_,
                                                    v_a_4016_,
                                                    v_a_4017_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_4280_) == 0 {
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_4280_,
                                                        1,
                                                    );
                                                    v___x_4281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropDown___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateForallPropDown___closed__14_once), _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__14);
                                                    crate::leanh::lean_inc_ref(v_body_4021_);
                                                    v___x_4282_ = l_Lean_mkApp3(
                                                        v___x_4281_,
                                                        v_binderType_4020_,
                                                        v_body_4021_,
                                                        v_a_4277_,
                                                    );
                                                    v___x_4283_ =
                                                        l_Lean_Meta_Grind_pushEqFalse___redArg(
                                                            v_body_4021_,
                                                            v___x_4282_,
                                                            v_a_4008_,
                                                            v_a_4010_,
                                                            v_a_4012_,
                                                            v_a_4014_,
                                                            v_a_4015_,
                                                            v_a_4016_,
                                                            v_a_4017_,
                                                        );
                                                    return v___x_4283_;
                                                } else {
                                                    crate::leanh::lean_dec(v_a_4277_);
                                                    crate::leanh::lean_dec_ref(v_body_4021_);
                                                    crate::leanh::lean_dec_ref(v_binderType_4020_);
                                                    return v___x_4280_;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_body_4021_);
                                                crate::leanh::lean_dec_ref(v_binderType_4020_);
                                                v_a_4284_ =
                                                    crate::leanh::lean_ctor_get(v___x_4276_, 0);
                                                v_isSharedCheck_4291_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4276_))
                                                        as u8;
                                                if v_isSharedCheck_4291_ == 0 {
                                                    v___x_4286_ = v___x_4276_;
                                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                                    state = 41;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4284_);
                                                    crate::leanh::lean_dec(v___x_4276_);
                                                    v___x_4286_ = crate::leanh::lean_box(0);
                                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                                    state = 41;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            state = 34;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4228_);
                                    state = 34;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                                v_a_4292_ = crate::leanh::lean_ctor_get(v___x_4227_, 0);
                                v_isSharedCheck_4299_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4227_)) as u8;
                                if v_isSharedCheck_4299_ == 0 {
                                    v___x_4294_ = v___x_4227_;
                                    v_isShared_4295_ = v_isSharedCheck_4299_;
                                    state = 43;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4292_);
                                    crate::leanh::lean_dec(v___x_4227_);
                                    v___x_4294_ = crate::leanh::lean_box(0);
                                    v_isShared_4295_ = v_isSharedCheck_4299_;
                                    state = 43;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                        v_a_4300_ = crate::leanh::lean_ctor_get(v___x_4131_, 0);
                        v_isSharedCheck_4307_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4131_)) as u8;
                        if v_isSharedCheck_4307_ == 0 {
                            v___x_4302_ = v___x_4131_;
                            v_isShared_4303_ = v_isSharedCheck_4307_;
                            state = 45;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4300_);
                            crate::leanh::lean_dec(v___x_4131_);
                            v___x_4302_ = crate::leanh::lean_box(0);
                            v_isShared_4303_ = v_isSharedCheck_4307_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4007_);
                    v___x_4308_ = crate::leanh::lean_box(0);
                    v___x_4309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4309_, 0, v___x_4308_);
                    return v___x_4309_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4034_) == 0 {
                    v_a_4035_ = crate::leanh::lean_ctor_get(v___y_4034_, 0);
                    v_isSharedCheck_4067_ = (!crate::leanh::lean_is_exclusive(v___y_4034_)) as u8;
                    if v_isSharedCheck_4067_ == 0 {
                        v___x_4037_ = v___y_4034_;
                        v_isShared_4038_ = v_isSharedCheck_4067_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4035_);
                        crate::leanh::lean_dec(v___y_4034_);
                        v___x_4037_ = crate::leanh::lean_box(0);
                        v_isShared_4038_ = v_isSharedCheck_4067_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_4021_);
                    crate::leanh::lean_dec_ref(v_binderType_4020_);
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    v_a_4068_ = crate::leanh::lean_ctor_get(v___y_4034_, 0);
                    v_isSharedCheck_4075_ = (!crate::leanh::lean_is_exclusive(v___y_4034_)) as u8;
                    if v_isSharedCheck_4075_ == 0 {
                        v___x_4070_ = v___y_4034_;
                        v_isShared_4071_ = v_isSharedCheck_4075_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4068_);
                        crate::leanh::lean_dec(v___y_4034_);
                        v___x_4070_ = crate::leanh::lean_box(0);
                        v_isShared_4071_ = v_isSharedCheck_4075_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4039_ = (crate::leanh::lean_unbox(v_a_4035_) as u8);
                crate::leanh::lean_dec(v_a_4035_);
                if v___x_4039_ == 0 {
                    crate::leanh::lean_dec_ref(v_body_4021_);
                    crate::leanh::lean_dec_ref(v_binderType_4020_);
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    v___x_4040_ = crate::leanh::lean_box(0);
                    if v_isShared_4038_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4037_, 0, v___x_4040_);
                        v___x_4042_ = v___x_4037_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4043_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4043_, 0, v___x_4040_);
                        v___x_4042_ = v_reuseFailAlloc_4043_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4037_);
                    v___x_4044_ = l_Lean_Meta_Grind_mkEqTrueProof(
                        v_e_4007_,
                        v___y_4028_,
                        v___y_4032_,
                        v___y_4030_,
                        v___y_4031_,
                        v___y_4026_,
                        v___y_4025_,
                        v___y_4027_,
                        v___y_4033_,
                        v___y_4029_,
                        v___y_4024_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4044_) == 0 {
                        v_a_4045_ = crate::leanh::lean_ctor_get(v___x_4044_, 0);
                        crate::leanh::lean_inc(v_a_4045_);
                        crate::leanh::lean_dec_ref_known(v___x_4044_, 1);
                        crate::leanh::lean_inc_ref(v_body_4021_);
                        v___x_4046_ = l_Lean_Meta_Grind_mkEqFalseProof(
                            v_body_4021_,
                            v___y_4028_,
                            v___y_4032_,
                            v___y_4030_,
                            v___y_4031_,
                            v___y_4026_,
                            v___y_4025_,
                            v___y_4027_,
                            v___y_4033_,
                            v___y_4029_,
                            v___y_4024_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4046_) == 0 {
                            v_a_4047_ = crate::leanh::lean_ctor_get(v___x_4046_, 0);
                            crate::leanh::lean_inc(v_a_4047_);
                            crate::leanh::lean_dec_ref_known(v___x_4046_, 1);
                            v___x_4048_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
                            crate::leanh::lean_inc_ref(v_binderType_4020_);
                            v___x_4049_ = l_Lean_mkApp4(
                                v___x_4048_,
                                v_binderType_4020_,
                                v_body_4021_,
                                v_a_4045_,
                                v_a_4047_,
                            );
                            v___x_4050_ = l_Lean_Meta_Grind_pushEqFalse___redArg(
                                v_binderType_4020_,
                                v___x_4049_,
                                v___y_4028_,
                                v___y_4030_,
                                v___y_4026_,
                                v___y_4027_,
                                v___y_4033_,
                                v___y_4029_,
                                v___y_4024_,
                            );
                            return v___x_4050_;
                        } else {
                            crate::leanh::lean_dec(v_a_4045_);
                            crate::leanh::lean_dec_ref(v_body_4021_);
                            crate::leanh::lean_dec_ref(v_binderType_4020_);
                            v_a_4051_ = crate::leanh::lean_ctor_get(v___x_4046_, 0);
                            v_isSharedCheck_4058_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4046_)) as u8;
                            if v_isSharedCheck_4058_ == 0 {
                                v___x_4053_ = v___x_4046_;
                                v_isShared_4054_ = v_isSharedCheck_4058_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4051_);
                                crate::leanh::lean_dec(v___x_4046_);
                                v___x_4053_ = crate::leanh::lean_box(0);
                                v_isShared_4054_ = v_isSharedCheck_4058_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_4021_);
                        crate::leanh::lean_dec_ref(v_binderType_4020_);
                        v_a_4059_ = crate::leanh::lean_ctor_get(v___x_4044_, 0);
                        v_isSharedCheck_4066_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4044_)) as u8;
                        if v_isSharedCheck_4066_ == 0 {
                            v___x_4061_ = v___x_4044_;
                            v_isShared_4062_ = v_isSharedCheck_4066_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4059_);
                            crate::leanh::lean_dec(v___x_4044_);
                            v___x_4061_ = crate::leanh::lean_box(0);
                            v_isShared_4062_ = v_isSharedCheck_4066_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_4042_;
            }
            4 => {
                if v_isShared_4054_ == 0 {
                    v___x_4056_ = v___x_4053_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4051_);
                    v___x_4056_ = v_reuseFailAlloc_4057_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4056_;
            }
            6 => {
                if v_isShared_4062_ == 0 {
                    v___x_4064_ = v___x_4061_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
                    v___x_4064_ = v_reuseFailAlloc_4065_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4064_;
            }
            8 => {
                if v_isShared_4071_ == 0 {
                    v___x_4073_ = v___x_4070_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_a_4068_);
                    v___x_4073_ = v_reuseFailAlloc_4074_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4073_;
            }
            10 => {
                v___x_4087_ = l_Lean_Expr_hasLooseBVars(v_body_4021_);
                if v___x_4087_ == 0 {
                    crate::leanh::lean_inc_ref(v_body_4021_);
                    crate::leanh::lean_inc_ref(v_binderType_4020_);
                    v___x_4088_ =
                        l_Lean_Meta_Grind_alreadyInternalized___redArg(v_body_4021_, v___y_4077_);
                    if crate::leanh::lean_obj_tag(v___x_4088_) == 0 {
                        v_a_4089_ = crate::leanh::lean_ctor_get(v___x_4088_, 0);
                        v_isSharedCheck_4102_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4088_)) as u8;
                        if v_isSharedCheck_4102_ == 0 {
                            v___x_4091_ = v___x_4088_;
                            v_isShared_4092_ = v_isSharedCheck_4102_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4089_);
                            crate::leanh::lean_dec(v___x_4088_);
                            v___x_4091_ = crate::leanh::lean_box(0);
                            v_isShared_4092_ = v_isSharedCheck_4102_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_4021_);
                        crate::leanh::lean_dec_ref(v_binderType_4020_);
                        crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                        v_a_4103_ = crate::leanh::lean_ctor_get(v___x_4088_, 0);
                        v_isSharedCheck_4110_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4088_)) as u8;
                        if v_isSharedCheck_4110_ == 0 {
                            v___x_4105_ = v___x_4088_;
                            v_isShared_4106_ = v_isSharedCheck_4110_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4103_);
                            crate::leanh::lean_dec(v___x_4088_);
                            v___x_4105_ = crate::leanh::lean_box(0);
                            v_isShared_4106_ = v_isSharedCheck_4110_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_binderType_4020_);
                    v___x_4111_ = l_Lean_Meta_isProp(
                        v_binderType_4020_,
                        v___y_4083_,
                        v___y_4084_,
                        v___y_4085_,
                        v___y_4086_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4111_) == 0 {
                        v_a_4112_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
                        v_isSharedCheck_4122_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4111_)) as u8;
                        if v_isSharedCheck_4122_ == 0 {
                            v___x_4114_ = v___x_4111_;
                            v_isShared_4115_ = v_isSharedCheck_4122_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4112_);
                            crate::leanh::lean_dec(v___x_4111_);
                            v___x_4114_ = crate::leanh::lean_box(0);
                            v_isShared_4115_ = v_isSharedCheck_4122_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                        v_a_4123_ = crate::leanh::lean_ctor_get(v___x_4111_, 0);
                        v_isSharedCheck_4130_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4111_)) as u8;
                        if v_isSharedCheck_4130_ == 0 {
                            v___x_4125_ = v___x_4111_;
                            v_isShared_4126_ = v_isSharedCheck_4130_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4123_);
                            crate::leanh::lean_dec(v___x_4111_);
                            v___x_4125_ = crate::leanh::lean_box(0);
                            v_isShared_4126_ = v_isSharedCheck_4130_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v___x_4093_ = (crate::leanh::lean_unbox(v_a_4089_) as u8);
                crate::leanh::lean_dec(v_a_4089_);
                if v___x_4093_ == 0 {
                    crate::leanh::lean_dec_ref(v_body_4021_);
                    crate::leanh::lean_dec_ref(v_binderType_4020_);
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    v___x_4094_ = crate::leanh::lean_box(0);
                    if v_isShared_4092_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4091_, 0, v___x_4094_);
                        v___x_4096_ = v___x_4091_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v___x_4094_);
                        v___x_4096_ = v_reuseFailAlloc_4097_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4091_);
                    crate::leanh::lean_inc_ref(v_body_4021_);
                    v___x_4098_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                        v_body_4021_,
                        v___y_4077_,
                        v___y_4081_,
                        v___y_4083_,
                        v___y_4084_,
                        v___y_4085_,
                        v___y_4086_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4098_) == 0 {
                        v_a_4099_ = crate::leanh::lean_ctor_get(v___x_4098_, 0);
                        crate::leanh::lean_inc(v_a_4099_);
                        v___x_4100_ = (crate::leanh::lean_unbox(v_a_4099_) as u8);
                        crate::leanh::lean_dec(v_a_4099_);
                        if v___x_4100_ == 0 {
                            v___y_4024_ = v___y_4086_;
                            v___y_4025_ = v___y_4082_;
                            v___y_4026_ = v___y_4081_;
                            v___y_4027_ = v___y_4083_;
                            v___y_4028_ = v___y_4077_;
                            v___y_4029_ = v___y_4085_;
                            v___y_4030_ = v___y_4079_;
                            v___y_4031_ = v___y_4080_;
                            v___y_4032_ = v___y_4078_;
                            v___y_4033_ = v___y_4084_;
                            v___y_4034_ = v___x_4098_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4098_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_4020_);
                            v___x_4101_ = l_Lean_Meta_isProp(
                                v_binderType_4020_,
                                v___y_4083_,
                                v___y_4084_,
                                v___y_4085_,
                                v___y_4086_,
                            );
                            v___y_4024_ = v___y_4086_;
                            v___y_4025_ = v___y_4082_;
                            v___y_4026_ = v___y_4081_;
                            v___y_4027_ = v___y_4083_;
                            v___y_4028_ = v___y_4077_;
                            v___y_4029_ = v___y_4085_;
                            v___y_4030_ = v___y_4079_;
                            v___y_4031_ = v___y_4080_;
                            v___y_4032_ = v___y_4078_;
                            v___y_4033_ = v___y_4084_;
                            v___y_4034_ = v___x_4101_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_4024_ = v___y_4086_;
                        v___y_4025_ = v___y_4082_;
                        v___y_4026_ = v___y_4081_;
                        v___y_4027_ = v___y_4083_;
                        v___y_4028_ = v___y_4077_;
                        v___y_4029_ = v___y_4085_;
                        v___y_4030_ = v___y_4079_;
                        v___y_4031_ = v___y_4080_;
                        v___y_4032_ = v___y_4078_;
                        v___y_4033_ = v___y_4084_;
                        v___y_4034_ = v___x_4098_;
                        state = 1;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_4096_;
            }
            13 => {
                if v_isShared_4106_ == 0 {
                    v___x_4108_ = v___x_4105_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
                    v___x_4108_ = v_reuseFailAlloc_4109_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4108_;
            }
            15 => {
                v___x_4116_ = (crate::leanh::lean_unbox(v_a_4112_) as u8);
                crate::leanh::lean_dec(v_a_4112_);
                if v___x_4116_ == 0 {
                    crate::leanh::lean_del_object(v___x_4114_);
                    v___x_4117_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(v_e_4007_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
                    return v___x_4117_;
                } else {
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    v___x_4118_ = crate::leanh::lean_box(0);
                    if v_isShared_4115_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4114_, 0, v___x_4118_);
                        v___x_4120_ = v___x_4114_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_4121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___x_4118_);
                        v___x_4120_ = v_reuseFailAlloc_4121_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_4120_;
            }
            17 => {
                if v_isShared_4126_ == 0 {
                    v___x_4128_ = v___x_4125_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
                    v___x_4128_ = v_reuseFailAlloc_4129_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4128_;
            }
            19 => {
                v___x_4139_ = (crate::leanh::lean_unbox(v_a_4135_) as u8);
                crate::leanh::lean_dec(v_a_4135_);
                if v___x_4139_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    v___x_4140_ = crate::leanh::lean_box(0);
                    if v_isShared_4138_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4137_, 0, v___x_4140_);
                        v___x_4142_ = v___x_4137_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_4143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_4140_);
                        v___x_4142_ = v_reuseFailAlloc_4143_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4137_);
                    crate::leanh::lean_inc_ref(v_e_4007_);
                    v___x_4144_ = l_Lean_Meta_Grind_eqResolution(
                        v_e_4007_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4144_) == 0 {
                        v_a_4145_ = crate::leanh::lean_ctor_get(v___x_4144_, 0);
                        crate::leanh::lean_inc(v_a_4145_);
                        crate::leanh::lean_dec_ref_known(v___x_4144_, 1);
                        if crate::leanh::lean_obj_tag(v_a_4145_) == 1 {
                            v_val_4146_ = crate::leanh::lean_ctor_get(v_a_4145_, 0);
                            v_isSharedCheck_4209_ =
                                (!crate::leanh::lean_is_exclusive(v_a_4145_)) as u8;
                            if v_isSharedCheck_4209_ == 0 {
                                v___x_4148_ = v_a_4145_;
                                v_isShared_4149_ = v_isSharedCheck_4209_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_4146_);
                                crate::leanh::lean_dec(v_a_4145_);
                                v___x_4148_ = crate::leanh::lean_box(0);
                                v_isShared_4149_ = v_isSharedCheck_4209_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4145_);
                            v___y_4077_ = v_a_4008_;
                            v___y_4078_ = v_a_4009_;
                            v___y_4079_ = v_a_4010_;
                            v___y_4080_ = v_a_4011_;
                            v___y_4081_ = v_a_4012_;
                            v___y_4082_ = v_a_4013_;
                            v___y_4083_ = v_a_4014_;
                            v___y_4084_ = v_a_4015_;
                            v___y_4085_ = v_a_4016_;
                            v___y_4086_ = v_a_4017_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                        v_a_4210_ = crate::leanh::lean_ctor_get(v___x_4144_, 0);
                        v_isSharedCheck_4217_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4144_)) as u8;
                        if v_isSharedCheck_4217_ == 0 {
                            v___x_4212_ = v___x_4144_;
                            v_isShared_4213_ = v_isSharedCheck_4217_;
                            state = 30;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4210_);
                            crate::leanh::lean_dec(v___x_4144_);
                            v___x_4212_ = crate::leanh::lean_box(0);
                            v_isShared_4213_ = v_isSharedCheck_4217_;
                            state = 30;
                            continue;
                        }
                    }
                }
            }
            20 => {
                return v___x_4142_;
            }
            21 => {
                v_fst_4150_ = crate::leanh::lean_ctor_get(v_val_4146_, 0);
                v_snd_4151_ = crate::leanh::lean_ctor_get(v_val_4146_, 1);
                v_isSharedCheck_4208_ = (!crate::leanh::lean_is_exclusive(v_val_4146_)) as u8;
                if v_isSharedCheck_4208_ == 0 {
                    v___x_4153_ = v_val_4146_;
                    v_isShared_4154_ = v_isSharedCheck_4208_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4151_);
                    crate::leanh::lean_inc(v_fst_4150_);
                    crate::leanh::lean_dec(v_val_4146_);
                    v___x_4153_ = crate::leanh::lean_box(0);
                    v_isShared_4154_ = v_isSharedCheck_4208_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v_options_4193_ = crate::leanh::lean_ctor_get(v_a_4016_, 2);
                v_hasTrace_4194_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_4193_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_4194_ == 0 {
                    crate::leanh::lean_del_object(v___x_4153_);
                    v___y_4156_ = v_a_4008_;
                    v___y_4157_ = v_a_4009_;
                    v___y_4158_ = v_a_4010_;
                    v___y_4159_ = v_a_4011_;
                    v___y_4160_ = v_a_4012_;
                    v___y_4161_ = v_a_4013_;
                    v___y_4162_ = v_a_4014_;
                    v___y_4163_ = v_a_4015_;
                    v___y_4164_ = v_a_4016_;
                    v___y_4165_ = v_a_4017_;
                    state = 23;
                    continue;
                } else {
                    v_inheritedTraceOptions_4195_ = crate::leanh::lean_ctor_get(v_a_4016_, 13);
                    v___x_4196_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
                    v___x_4197_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_propagateForallPropDown___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_propagateForallPropDown___closed__2_once
                        ),
                        _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2,
                    );
                    v___x_4198_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_4195_,
                        v_options_4193_,
                        v___x_4197_,
                    );
                    if v___x_4198_ == 0 {
                        crate::leanh::lean_del_object(v___x_4153_);
                        v___y_4156_ = v_a_4008_;
                        v___y_4157_ = v_a_4009_;
                        v___y_4158_ = v_a_4010_;
                        v___y_4159_ = v_a_4011_;
                        v___y_4160_ = v_a_4012_;
                        v___y_4161_ = v_a_4013_;
                        v___y_4162_ = v_a_4014_;
                        v___y_4163_ = v_a_4015_;
                        v___y_4164_ = v_a_4016_;
                        v___y_4165_ = v_a_4017_;
                        state = 23;
                        continue;
                    } else {
                        v___x_4199_ = l_Lean_Meta_Grind_updateLastTag(
                            v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_,
                            v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4199_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4199_, 1);
                            crate::leanh::lean_inc_ref(v_e_4007_);
                            v___x_4200_ = l_Lean_MessageData_ofExpr(v_e_4007_);
                            v___x_4201_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateForallPropDown___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateForallPropDown___closed__4_once
                                ),
                                _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4,
                            );
                            if v_isShared_4154_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4153_, 7);
                                crate::leanh::lean_ctor_set(v___x_4153_, 1, v___x_4201_);
                                crate::leanh::lean_ctor_set(v___x_4153_, 0, v___x_4200_);
                                v___x_4203_ = v___x_4153_;
                                state = 29;
                                continue;
                            } else {
                                v_reuseFailAlloc_4207_ =
                                    crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___x_4200_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4207_, 1, v___x_4201_);
                                v___x_4203_ = v_reuseFailAlloc_4207_;
                                state = 29;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4153_);
                            crate::leanh::lean_dec(v_snd_4151_);
                            crate::leanh::lean_dec(v_fst_4150_);
                            crate::leanh::lean_del_object(v___x_4148_);
                            crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                            return v___x_4199_;
                        }
                    }
                }
            }
            23 => {
                crate::leanh::lean_inc_ref(v_e_4007_);
                v___x_4166_ = l_Lean_Meta_Grind_mkEqTrueProof(
                    v_e_4007_,
                    v___y_4156_,
                    v___y_4157_,
                    v___y_4158_,
                    v___y_4159_,
                    v___y_4160_,
                    v___y_4161_,
                    v___y_4162_,
                    v___y_4163_,
                    v___y_4164_,
                    v___y_4165_,
                );
                if crate::leanh::lean_obj_tag(v___x_4166_) == 0 {
                    v_a_4167_ = crate::leanh::lean_ctor_get(v___x_4166_, 0);
                    crate::leanh::lean_inc(v_a_4167_);
                    crate::leanh::lean_dec_ref_known(v___x_4166_, 1);
                    v___x_4168_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4007_, v___y_4156_);
                    if crate::leanh::lean_obj_tag(v___x_4168_) == 0 {
                        v_a_4169_ = crate::leanh::lean_ctor_get(v___x_4168_, 0);
                        crate::leanh::lean_inc(v_a_4169_);
                        crate::leanh::lean_dec_ref_known(v___x_4168_, 1);
                        crate::leanh::lean_inc_ref_n(v_e_4007_, 2);
                        v___x_4170_ = l_Lean_Meta_mkOfEqTrueCore(v_e_4007_, v_a_4167_);
                        v___x_4171_ = l_Lean_Expr_app___override(v_snd_4151_, v___x_4170_);
                        if v_isShared_4149_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4148_, 4);
                            crate::leanh::lean_ctor_set(v___x_4148_, 0, v_e_4007_);
                            v___x_4173_ = v___x_4148_;
                            state = 24;
                            continue;
                        } else {
                            v_reuseFailAlloc_4176_ =
                                crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_e_4007_);
                            v___x_4173_ = v_reuseFailAlloc_4176_;
                            state = 24;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4167_);
                        crate::leanh::lean_dec(v_snd_4151_);
                        crate::leanh::lean_dec(v_fst_4150_);
                        crate::leanh::lean_del_object(v___x_4148_);
                        crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                        v_a_4177_ = crate::leanh::lean_ctor_get(v___x_4168_, 0);
                        v_isSharedCheck_4184_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4168_)) as u8;
                        if v_isSharedCheck_4184_ == 0 {
                            v___x_4179_ = v___x_4168_;
                            v_isShared_4180_ = v_isSharedCheck_4184_;
                            state = 25;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4177_);
                            crate::leanh::lean_dec(v___x_4168_);
                            v___x_4179_ = crate::leanh::lean_box(0);
                            v_isShared_4180_ = v_isSharedCheck_4184_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_4151_);
                    crate::leanh::lean_dec(v_fst_4150_);
                    crate::leanh::lean_del_object(v___x_4148_);
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    v_a_4185_ = crate::leanh::lean_ctor_get(v___x_4166_, 0);
                    v_isSharedCheck_4192_ = (!crate::leanh::lean_is_exclusive(v___x_4166_)) as u8;
                    if v_isSharedCheck_4192_ == 0 {
                        v___x_4187_ = v___x_4166_;
                        v_isShared_4188_ = v_isSharedCheck_4192_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4185_);
                        crate::leanh::lean_dec(v___x_4166_);
                        v___x_4187_ = crate::leanh::lean_box(0);
                        v_isShared_4188_ = v_isSharedCheck_4192_;
                        state = 27;
                        continue;
                    }
                }
            }
            24 => {
                v___x_4174_ = crate::leanh::lean_box(1);
                v___x_4175_ = l_Lean_Meta_Grind_addNewRawFact(
                    v___x_4171_,
                    v_fst_4150_,
                    v_a_4169_,
                    v___x_4173_,
                    v___x_4174_,
                    v___y_4156_,
                    v___y_4157_,
                    v___y_4158_,
                    v___y_4159_,
                    v___y_4160_,
                    v___y_4161_,
                    v___y_4162_,
                    v___y_4163_,
                    v___y_4164_,
                    v___y_4165_,
                );
                if crate::leanh::lean_obj_tag(v___x_4175_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4175_, 1);
                    v___y_4077_ = v___y_4156_;
                    v___y_4078_ = v___y_4157_;
                    v___y_4079_ = v___y_4158_;
                    v___y_4080_ = v___y_4159_;
                    v___y_4081_ = v___y_4160_;
                    v___y_4082_ = v___y_4161_;
                    v___y_4083_ = v___y_4162_;
                    v___y_4084_ = v___y_4163_;
                    v___y_4085_ = v___y_4164_;
                    v___y_4086_ = v___y_4165_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    return v___x_4175_;
                }
            }
            25 => {
                if v_isShared_4180_ == 0 {
                    v___x_4182_ = v___x_4179_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
                    v___x_4182_ = v_reuseFailAlloc_4183_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4182_;
            }
            27 => {
                if v_isShared_4188_ == 0 {
                    v___x_4190_ = v___x_4187_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
                    v___x_4190_ = v_reuseFailAlloc_4191_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4190_;
            }
            29 => {
                crate::leanh::lean_inc(v_fst_4150_);
                v___x_4204_ = l_Lean_MessageData_ofExpr(v_fst_4150_);
                v___x_4205_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4205_, 0, v___x_4203_);
                crate::leanh::lean_ctor_set(v___x_4205_, 1, v___x_4204_);
                v___x_4206_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(
                        v___x_4196_,
                        v___x_4205_,
                        v_a_4014_,
                        v_a_4015_,
                        v_a_4016_,
                        v_a_4017_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4206_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4206_, 1);
                    v___y_4156_ = v_a_4008_;
                    v___y_4157_ = v_a_4009_;
                    v___y_4158_ = v_a_4010_;
                    v___y_4159_ = v_a_4011_;
                    v___y_4160_ = v_a_4012_;
                    v___y_4161_ = v_a_4013_;
                    v___y_4162_ = v_a_4014_;
                    v___y_4163_ = v_a_4015_;
                    v___y_4164_ = v_a_4016_;
                    v___y_4165_ = v_a_4017_;
                    state = 23;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_4151_);
                    crate::leanh::lean_dec(v_fst_4150_);
                    crate::leanh::lean_del_object(v___x_4148_);
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    return v___x_4206_;
                }
            }
            30 => {
                if v_isShared_4213_ == 0 {
                    v___x_4215_ = v___x_4212_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
                    v___x_4215_ = v_reuseFailAlloc_4216_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4215_;
            }
            32 => {
                if v_isShared_4222_ == 0 {
                    v___x_4224_ = v___x_4221_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4225_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
                    v___x_4224_ = v_reuseFailAlloc_4225_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4224_;
            }
            34 => {
                crate::leanh::lean_inc_ref(v_binderType_4020_);
                v___x_4230_ = l_Lean_Meta_getLevel(
                    v_binderType_4020_,
                    v_a_4014_,
                    v_a_4015_,
                    v_a_4016_,
                    v_a_4017_,
                );
                if crate::leanh::lean_obj_tag(v___x_4230_) == 0 {
                    v_a_4231_ = crate::leanh::lean_ctor_get(v___x_4230_, 0);
                    crate::leanh::lean_inc(v_a_4231_);
                    crate::leanh::lean_dec_ref_known(v___x_4230_, 1);
                    crate::leanh::lean_inc_ref(v_e_4007_);
                    v___x_4232_ = l_Lean_Meta_Grind_mkEqFalseProof(
                        v_e_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_,
                        v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4232_) == 0 {
                        v_a_4233_ = crate::leanh::lean_ctor_get(v___x_4232_, 0);
                        crate::leanh::lean_inc(v_a_4233_);
                        crate::leanh::lean_dec_ref_known(v___x_4232_, 1);
                        crate::leanh::lean_inc_ref(v_body_4021_);
                        v___x_4234_ = l_Lean_mkNot(v_body_4021_);
                        crate::leanh::lean_inc_ref(v_binderType_4020_);
                        crate::leanh::lean_inc(v_binderName_4019_);
                        v___x_4235_ = l_Lean_mkLambda(
                            v_binderName_4019_,
                            v_binderInfo_4022_,
                            v_binderType_4020_,
                            v___x_4234_,
                        );
                        v___x_4236_ =
                            l_Lean_Meta_Grind_getGeneration___redArg(v_e_4007_, v_a_4008_);
                        if crate::leanh::lean_obj_tag(v___x_4236_) == 0 {
                            v_a_4237_ = crate::leanh::lean_ctor_get(v___x_4236_, 0);
                            crate::leanh::lean_inc(v_a_4237_);
                            crate::leanh::lean_dec_ref_known(v___x_4236_, 1);
                            v___x_4238_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
                            v___x_4239_ = crate::leanh::lean_box(0);
                            v___x_4240_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4240_, 0, v_a_4231_);
                            crate::leanh::lean_ctor_set(v___x_4240_, 1, v___x_4239_);
                            crate::leanh::lean_inc_ref(v___x_4240_);
                            v___x_4241_ = l_Lean_mkConst(v___x_4238_, v___x_4240_);
                            crate::leanh::lean_inc_ref_n(v_binderType_4020_, 3);
                            v___x_4242_ =
                                l_Lean_mkAppB(v___x_4241_, v_binderType_4020_, v___x_4235_);
                            crate::leanh::lean_inc_ref(v_body_4021_);
                            crate::leanh::lean_inc(v_binderName_4019_);
                            v___x_4243_ = l_Lean_mkLambda(
                                v_binderName_4019_,
                                v_binderInfo_4022_,
                                v_binderType_4020_,
                                v_body_4021_,
                            );
                            v___x_4244_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__8;
                            v___x_4245_ = l_Lean_mkConst(v___x_4244_, v___x_4240_);
                            v___x_4246_ = l_Lean_mkApp3(
                                v___x_4245_,
                                v_binderType_4020_,
                                v___x_4243_,
                                v_a_4233_,
                            );
                            v___x_4247_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4247_, 0, v_e_4007_);
                            v___x_4248_ = crate::leanh::lean_box(1);
                            v___x_4249_ = l_Lean_Meta_Grind_addNewRawFact(
                                v___x_4246_,
                                v___x_4242_,
                                v_a_4237_,
                                v___x_4247_,
                                v___x_4248_,
                                v_a_4008_,
                                v_a_4009_,
                                v_a_4010_,
                                v_a_4011_,
                                v_a_4012_,
                                v_a_4013_,
                                v_a_4014_,
                                v_a_4015_,
                                v_a_4016_,
                                v_a_4017_,
                            );
                            return v___x_4249_;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4235_);
                            crate::leanh::lean_dec(v_a_4233_);
                            crate::leanh::lean_dec(v_a_4231_);
                            crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                            v_a_4250_ = crate::leanh::lean_ctor_get(v___x_4236_, 0);
                            v_isSharedCheck_4257_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4236_)) as u8;
                            if v_isSharedCheck_4257_ == 0 {
                                v___x_4252_ = v___x_4236_;
                                v_isShared_4253_ = v_isSharedCheck_4257_;
                                state = 35;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4250_);
                                crate::leanh::lean_dec(v___x_4236_);
                                v___x_4252_ = crate::leanh::lean_box(0);
                                v_isShared_4253_ = v_isSharedCheck_4257_;
                                state = 35;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4231_);
                        crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                        v_a_4258_ = crate::leanh::lean_ctor_get(v___x_4232_, 0);
                        v_isSharedCheck_4265_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4232_)) as u8;
                        if v_isSharedCheck_4265_ == 0 {
                            v___x_4260_ = v___x_4232_;
                            v_isShared_4261_ = v_isSharedCheck_4265_;
                            state = 37;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4258_);
                            crate::leanh::lean_dec(v___x_4232_);
                            v___x_4260_ = crate::leanh::lean_box(0);
                            v_isShared_4261_ = v_isSharedCheck_4265_;
                            state = 37;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_e_4007_, 3);
                    v_a_4266_ = crate::leanh::lean_ctor_get(v___x_4230_, 0);
                    v_isSharedCheck_4273_ = (!crate::leanh::lean_is_exclusive(v___x_4230_)) as u8;
                    if v_isSharedCheck_4273_ == 0 {
                        v___x_4268_ = v___x_4230_;
                        v_isShared_4269_ = v_isSharedCheck_4273_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4266_);
                        crate::leanh::lean_dec(v___x_4230_);
                        v___x_4268_ = crate::leanh::lean_box(0);
                        v_isShared_4269_ = v_isSharedCheck_4273_;
                        state = 39;
                        continue;
                    }
                }
            }
            35 => {
                if v_isShared_4253_ == 0 {
                    v___x_4255_ = v___x_4252_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
                    v___x_4255_ = v_reuseFailAlloc_4256_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4255_;
            }
            37 => {
                if v_isShared_4261_ == 0 {
                    v___x_4263_ = v___x_4260_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
                    v___x_4263_ = v_reuseFailAlloc_4264_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4263_;
            }
            39 => {
                if v_isShared_4269_ == 0 {
                    v___x_4271_ = v___x_4268_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_4272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
                    v___x_4271_ = v_reuseFailAlloc_4272_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_4271_;
            }
            41 => {
                if v_isShared_4287_ == 0 {
                    v___x_4289_ = v___x_4286_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_4289_;
            }
            43 => {
                if v_isShared_4295_ == 0 {
                    v___x_4297_ = v___x_4294_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_4298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
                    v___x_4297_ = v_reuseFailAlloc_4298_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_4297_;
            }
            45 => {
                if v_isShared_4303_ == 0 {
                    v___x_4305_ = v___x_4302_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_4306_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
                    v___x_4305_ = v_reuseFailAlloc_4306_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_4305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateForallPropDown___boxed(
    mut v_e_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_a_4312_: *mut crate::leanh::LeanObject,
    mut v_a_4313_: *mut crate::leanh::LeanObject,
    mut v_a_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
    mut v_a_4316_: *mut crate::leanh::LeanObject,
    mut v_a_4317_: *mut crate::leanh::LeanObject,
    mut v_a_4318_: *mut crate::leanh::LeanObject,
    mut v_a_4319_: *mut crate::leanh::LeanObject,
    mut v_a_4320_: *mut crate::leanh::LeanObject,
    mut v_a_4321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4322_ = l_Lean_Meta_Grind_propagateForallPropDown(
        v_e_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_,
        v_a_4318_, v_a_4319_, v_a_4320_,
    );
    crate::leanh::lean_dec(v_a_4320_);
    crate::leanh::lean_dec_ref(v_a_4319_);
    crate::leanh::lean_dec(v_a_4318_);
    crate::leanh::lean_dec_ref(v_a_4317_);
    crate::leanh::lean_dec(v_a_4316_);
    crate::leanh::lean_dec_ref(v_a_4315_);
    crate::leanh::lean_dec(v_a_4314_);
    crate::leanh::lean_dec_ref(v_a_4313_);
    crate::leanh::lean_dec(v_a_4312_);
    crate::leanh::lean_dec(v_a_4311_);
    return v_res_4322_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4326_ = crate::leanh::lean_box(0);
    v___x_4327_ = l_Lean_Meta_Grind_propagateExistsDown___closed__1;
    v___x_4328_ = l_Lean_mkConst(v___x_4327_, v___x_4326_);
    return v___x_4328_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4329_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4330_ = l_Lean_Expr_bvar___override(v___x_4329_);
    return v___x_4330_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateExistsDown(
    mut v_e_4337_: *mut crate::leanh::LeanObject,
    mut v_a_4338_: *mut crate::leanh::LeanObject,
    mut v_a_4339_: *mut crate::leanh::LeanObject,
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_a_4341_: *mut crate::leanh::LeanObject,
    mut v_a_4342_: *mut crate::leanh::LeanObject,
    mut v_a_4343_: *mut crate::leanh::LeanObject,
    mut v_a_4344_: *mut crate::leanh::LeanObject,
    mut v_a_4345_: *mut crate::leanh::LeanObject,
    mut v_a_4346_: *mut crate::leanh::LeanObject,
    mut v_a_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4356_: u8 = 0;
    let mut v___x_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: u8 = 0;
    let mut v_arg_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    let mut v_arg_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: u8 = 0;
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4394_: u8 = 0;
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4398_: u8 = 0;
    let mut v_a_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut v_a_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4411_: u8 = 0;
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_4337_);
                v___x_4352_ = l_Lean_Meta_Grind_isEqFalse___redArg(
                    v_e_4337_, v_a_4338_, v_a_4342_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_,
                );
                if crate::leanh::lean_obj_tag(v___x_4352_) == 0 {
                    v_a_4353_ = crate::leanh::lean_ctor_get(v___x_4352_, 0);
                    v_isSharedCheck_4407_ = (!crate::leanh::lean_is_exclusive(v___x_4352_)) as u8;
                    if v_isSharedCheck_4407_ == 0 {
                        v___x_4355_ = v___x_4352_;
                        v_isShared_4356_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4353_);
                        crate::leanh::lean_dec(v___x_4352_);
                        v___x_4355_ = crate::leanh::lean_box(0);
                        v_isShared_4356_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4337_);
                    v_a_4408_ = crate::leanh::lean_ctor_get(v___x_4352_, 0);
                    v_isSharedCheck_4415_ = (!crate::leanh::lean_is_exclusive(v___x_4352_)) as u8;
                    if v_isSharedCheck_4415_ == 0 {
                        v___x_4410_ = v___x_4352_;
                        v_isShared_4411_ = v_isSharedCheck_4415_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4408_);
                        crate::leanh::lean_dec(v___x_4352_);
                        v___x_4410_ = crate::leanh::lean_box(0);
                        v_isShared_4411_ = v_isSharedCheck_4415_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4350_ = crate::leanh::lean_box(0);
                v___x_4351_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4351_, 0, v___x_4350_);
                return v___x_4351_;
            }
            2 => {
                v___x_4357_ = (crate::leanh::lean_unbox(v_a_4353_) as u8);
                crate::leanh::lean_dec(v_a_4353_);
                if v___x_4357_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_4337_);
                    v___x_4358_ = crate::leanh::lean_box(0);
                    if v_isShared_4356_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4355_, 0, v___x_4358_);
                        v___x_4360_ = v___x_4355_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___x_4358_);
                        v___x_4360_ = v_reuseFailAlloc_4361_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4355_);
                    crate::leanh::lean_inc_ref(v_e_4337_);
                    v___x_4362_ = l_Lean_Expr_cleanupAnnotations(v_e_4337_);
                    v___x_4363_ = l_Lean_Expr_isApp(v___x_4362_);
                    if v___x_4363_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4362_);
                        crate::leanh::lean_dec_ref(v_e_4337_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_4364_ = crate::leanh::lean_ctor_get(v___x_4362_, 1);
                        crate::leanh::lean_inc_ref(v_arg_4364_);
                        v___x_4365_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4362_);
                        v___x_4366_ = l_Lean_Expr_isApp(v___x_4365_);
                        if v___x_4366_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_4365_);
                            crate::leanh::lean_dec_ref(v_arg_4364_);
                            crate::leanh::lean_dec_ref(v_e_4337_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_4367_ = crate::leanh::lean_ctor_get(v___x_4365_, 1);
                            crate::leanh::lean_inc_ref(v_arg_4367_);
                            v___x_4368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4365_);
                            v___x_4369_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
                            v___x_4370_ = l_Lean_Expr_isConstOf(v___x_4368_, v___x_4369_);
                            if v___x_4370_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4368_);
                                crate::leanh::lean_dec_ref(v_arg_4367_);
                                crate::leanh::lean_dec_ref(v_arg_4364_);
                                crate::leanh::lean_dec_ref(v_e_4337_);
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_e_4337_);
                                v___x_4371_ = l_Lean_Meta_Grind_mkEqFalseProof(
                                    v_e_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_,
                                    v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_,
                                    v_a_4347_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4371_) == 0 {
                                    v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4371_, 0);
                                    crate::leanh::lean_inc(v_a_4372_);
                                    crate::leanh::lean_dec_ref_known(v___x_4371_, 1);
                                    v___x_4373_ = l_Lean_Meta_Grind_getGeneration___redArg(
                                        v_e_4337_, v_a_4338_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4373_) == 0 {
                                        v_a_4374_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                                        crate::leanh::lean_inc(v_a_4374_);
                                        crate::leanh::lean_dec_ref_known(v___x_4373_, 1);
                                        v___x_4375_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateExistsDown___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateExistsDown___closed__2_once), _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2);
                                        v___x_4376_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateExistsDown___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateExistsDown___closed__3_once), _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3);
                                        crate::leanh::lean_inc_ref(v_arg_4364_);
                                        v___x_4377_ =
                                            l_Lean_Expr_app___override(v_arg_4364_, v___x_4376_);
                                        v___x_4378_ = l_Lean_Expr_headBeta(v___x_4377_);
                                        v___x_4379_ =
                                            l_Lean_Expr_app___override(v___x_4375_, v___x_4378_);
                                        v___x_4380_ =
                                            l_Lean_Meta_Grind_propagateExistsDown___closed__5;
                                        v___x_4381_ = 0;
                                        crate::leanh::lean_inc_ref(v_arg_4367_);
                                        v___x_4382_ = l_Lean_mkForall(
                                            v___x_4380_,
                                            v___x_4381_,
                                            v_arg_4367_,
                                            v___x_4379_,
                                        );
                                        v___x_4383_ = l_Lean_Expr_constLevels_x21(v___x_4368_);
                                        crate::leanh::lean_dec_ref(v___x_4368_);
                                        v___x_4384_ =
                                            l_Lean_Meta_Grind_propagateExistsDown___closed__7;
                                        v___x_4385_ = l_Lean_mkConst(v___x_4384_, v___x_4383_);
                                        crate::leanh::lean_inc_ref(v_e_4337_);
                                        v___x_4386_ =
                                            l_Lean_Meta_mkOfEqFalseCore(v_e_4337_, v_a_4372_);
                                        v___x_4387_ = l_Lean_mkApp3(
                                            v___x_4385_,
                                            v_arg_4367_,
                                            v_arg_4364_,
                                            v___x_4386_,
                                        );
                                        v___x_4388_ =
                                            crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4388_, 0, v_e_4337_);
                                        v___x_4389_ = crate::leanh::lean_box(1);
                                        v___x_4390_ = l_Lean_Meta_Grind_addNewRawFact(
                                            v___x_4387_,
                                            v___x_4382_,
                                            v_a_4374_,
                                            v___x_4388_,
                                            v___x_4389_,
                                            v_a_4338_,
                                            v_a_4339_,
                                            v_a_4340_,
                                            v_a_4341_,
                                            v_a_4342_,
                                            v_a_4343_,
                                            v_a_4344_,
                                            v_a_4345_,
                                            v_a_4346_,
                                            v_a_4347_,
                                        );
                                        return v___x_4390_;
                                    } else {
                                        crate::leanh::lean_dec(v_a_4372_);
                                        crate::leanh::lean_dec_ref(v___x_4368_);
                                        crate::leanh::lean_dec_ref(v_arg_4367_);
                                        crate::leanh::lean_dec_ref(v_arg_4364_);
                                        crate::leanh::lean_dec_ref(v_e_4337_);
                                        v_a_4391_ = crate::leanh::lean_ctor_get(v___x_4373_, 0);
                                        v_isSharedCheck_4398_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4373_)) as u8;
                                        if v_isSharedCheck_4398_ == 0 {
                                            v___x_4393_ = v___x_4373_;
                                            v_isShared_4394_ = v_isSharedCheck_4398_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4391_);
                                            crate::leanh::lean_dec(v___x_4373_);
                                            v___x_4393_ = crate::leanh::lean_box(0);
                                            v_isShared_4394_ = v_isSharedCheck_4398_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4368_);
                                    crate::leanh::lean_dec_ref(v_arg_4367_);
                                    crate::leanh::lean_dec_ref(v_arg_4364_);
                                    crate::leanh::lean_dec_ref(v_e_4337_);
                                    v_a_4399_ = crate::leanh::lean_ctor_get(v___x_4371_, 0);
                                    v_isSharedCheck_4406_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4371_)) as u8;
                                    if v_isSharedCheck_4406_ == 0 {
                                        v___x_4401_ = v___x_4371_;
                                        v_isShared_4402_ = v_isSharedCheck_4406_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4399_);
                                        crate::leanh::lean_dec(v___x_4371_);
                                        v___x_4401_ = crate::leanh::lean_box(0);
                                        v_isShared_4402_ = v_isSharedCheck_4406_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_4360_;
            }
            4 => {
                if v_isShared_4394_ == 0 {
                    v___x_4396_ = v___x_4393_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
                    v___x_4396_ = v_reuseFailAlloc_4397_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4396_;
            }
            6 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4404_;
            }
            8 => {
                if v_isShared_4411_ == 0 {
                    v___x_4413_ = v___x_4410_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
                    v___x_4413_ = v_reuseFailAlloc_4414_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateExistsDown___boxed(
    mut v_e_4416_: *mut crate::leanh::LeanObject,
    mut v_a_4417_: *mut crate::leanh::LeanObject,
    mut v_a_4418_: *mut crate::leanh::LeanObject,
    mut v_a_4419_: *mut crate::leanh::LeanObject,
    mut v_a_4420_: *mut crate::leanh::LeanObject,
    mut v_a_4421_: *mut crate::leanh::LeanObject,
    mut v_a_4422_: *mut crate::leanh::LeanObject,
    mut v_a_4423_: *mut crate::leanh::LeanObject,
    mut v_a_4424_: *mut crate::leanh::LeanObject,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v_a_4426_: *mut crate::leanh::LeanObject,
    mut v_a_4427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4428_ = l_Lean_Meta_Grind_propagateExistsDown(
        v_e_4416_, v_a_4417_, v_a_4418_, v_a_4419_, v_a_4420_, v_a_4421_, v_a_4422_, v_a_4423_,
        v_a_4424_, v_a_4425_, v_a_4426_,
    );
    crate::leanh::lean_dec(v_a_4426_);
    crate::leanh::lean_dec_ref(v_a_4425_);
    crate::leanh::lean_dec(v_a_4424_);
    crate::leanh::lean_dec_ref(v_a_4423_);
    crate::leanh::lean_dec(v_a_4422_);
    crate::leanh::lean_dec_ref(v_a_4421_);
    crate::leanh::lean_dec(v_a_4420_);
    crate::leanh::lean_dec_ref(v_a_4419_);
    crate::leanh::lean_dec(v_a_4418_);
    crate::leanh::lean_dec(v_a_4417_);
    return v_res_4428_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4430_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
    v___x_4431_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_propagateExistsDown___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_4432_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_4430_, v___x_4431_);
    return v___x_4432_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8____boxed(
    mut v_a_4433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4434_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8_();
    return v_res_4434_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4441_ = crate::leanh::lean_box(0);
    v___x_4442_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
    v___x_4443_ = l_Lean_mkConst(v___x_4442_, v___x_4441_);
    return v___x_4443_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(
    mut v_e_4444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_e_4444_) == 7 {
        let mut v_binderName_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_binderType_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_binderName_4445_ = crate::leanh::lean_ctor_get(v_e_4444_, 0);
        v_binderType_4446_ = crate::leanh::lean_ctor_get(v_e_4444_, 1);
        v_body_4447_ = crate::leanh::lean_ctor_get(v_e_4444_, 2);
        crate::leanh::lean_inc_ref(v_body_4447_);
        crate::leanh::lean_inc_ref(v_binderType_4446_);
        v___x_4448_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4448_, 0, v_binderType_4446_);
        crate::leanh::lean_ctor_set(v___x_4448_, 1, v_body_4447_);
        crate::leanh::lean_inc(v_binderName_4445_);
        v___x_4449_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4449_, 0, v_binderName_4445_);
        crate::leanh::lean_ctor_set(v___x_4449_, 1, v___x_4448_);
        v___x_4450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4450_, 0, v___x_4449_);
        return v___x_4450_;
    } else {
        let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4453_: u8 = 0;
        v___x_4451_ = l_Lean_Meta_Grind_propagateExistsDown___closed__1;
        v___x_4452_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4453_ = l_Lean_Expr_isAppOfArity(v_e_4444_, v___x_4451_, v___x_4452_);
        if v___x_4453_ == 0 {
            let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4454_ = crate::leanh::lean_box(0);
            return v___x_4454_;
        } else {
            let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4455_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1;
            v___x_4456_ = l_Lean_Expr_appArg_x21(v_e_4444_);
            v___x_4457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
            v___x_4458_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4458_, 0, v___x_4456_);
            crate::leanh::lean_ctor_set(v___x_4458_, 1, v___x_4457_);
            v___x_4459_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4459_, 0, v___x_4455_);
            crate::leanh::lean_ctor_set(v___x_4459_, 1, v___x_4458_);
            v___x_4460_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4460_, 0, v___x_4459_);
            return v___x_4460_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(
    mut v_e_4461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4462_ =
        l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(
            v_e_4461_,
        );
    crate::leanh::lean_dec_ref(v_e_4461_);
    return v_res_4462_;
}
pub unsafe fn l_Lean_Meta_Grind_simpForall___lam__0(
    mut v_fst_4463_: *mut crate::leanh::LeanObject,
    mut v_a_4464_: *mut crate::leanh::LeanObject,
    mut v___y_4465_: *mut crate::leanh::LeanObject,
    mut v___y_4466_: *mut crate::leanh::LeanObject,
    mut v___y_4467_: *mut crate::leanh::LeanObject,
    mut v___y_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4473_ = lean_expr_instantiate1(v_fst_4463_, v_a_4464_);
    v___x_4474_ = l_Lean_Meta_getLevel(
        v___x_4473_,
        v___y_4468_,
        v___y_4469_,
        v___y_4470_,
        v___y_4471_,
    );
    return v___x_4474_;
}
pub unsafe fn l_Lean_Meta_Grind_simpForall___lam__0___boxed(
    mut v_fst_4475_: *mut crate::leanh::LeanObject,
    mut v_a_4476_: *mut crate::leanh::LeanObject,
    mut v___y_4477_: *mut crate::leanh::LeanObject,
    mut v___y_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
    mut v___y_4482_: *mut crate::leanh::LeanObject,
    mut v___y_4483_: *mut crate::leanh::LeanObject,
    mut v___y_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4485_ = l_Lean_Meta_Grind_simpForall___lam__0(
        v_fst_4475_,
        v_a_4476_,
        v___y_4477_,
        v___y_4478_,
        v___y_4479_,
        v___y_4480_,
        v___y_4481_,
        v___y_4482_,
        v___y_4483_,
    );
    crate::leanh::lean_dec(v___y_4483_);
    crate::leanh::lean_dec_ref(v___y_4482_);
    crate::leanh::lean_dec(v___y_4481_);
    crate::leanh::lean_dec_ref(v___y_4480_);
    crate::leanh::lean_dec(v___y_4479_);
    crate::leanh::lean_dec_ref(v___y_4478_);
    crate::leanh::lean_dec(v___y_4477_);
    crate::leanh::lean_dec_ref(v_a_4476_);
    crate::leanh::lean_dec_ref(v_fst_4475_);
    return v_res_4485_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(
    mut v_k_4486_: *mut crate::leanh::LeanObject,
    mut v___y_4487_: *mut crate::leanh::LeanObject,
    mut v___y_4488_: *mut crate::leanh::LeanObject,
    mut v___y_4489_: *mut crate::leanh::LeanObject,
    mut v_b_4490_: *mut crate::leanh::LeanObject,
    mut v___y_4491_: *mut crate::leanh::LeanObject,
    mut v___y_4492_: *mut crate::leanh::LeanObject,
    mut v___y_4493_: *mut crate::leanh::LeanObject,
    mut v___y_4494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4494_);
    crate::leanh::lean_inc_ref(v___y_4493_);
    crate::leanh::lean_inc(v___y_4492_);
    crate::leanh::lean_inc_ref(v___y_4491_);
    crate::leanh::lean_inc(v___y_4489_);
    crate::leanh::lean_inc_ref(v___y_4488_);
    crate::leanh::lean_inc(v___y_4487_);
    v___x_4496_ = crate::leanh::lean_apply_9(
        v_k_4486_,
        v_b_4490_,
        v___y_4487_,
        v___y_4488_,
        v___y_4489_,
        v___y_4491_,
        v___y_4492_,
        v___y_4493_,
        v___y_4494_,
        crate::leanh::lean_box(0),
    );
    return v___x_4496_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_4497_: *mut crate::leanh::LeanObject,
    mut v___y_4498_: *mut crate::leanh::LeanObject,
    mut v___y_4499_: *mut crate::leanh::LeanObject,
    mut v___y_4500_: *mut crate::leanh::LeanObject,
    mut v_b_4501_: *mut crate::leanh::LeanObject,
    mut v___y_4502_: *mut crate::leanh::LeanObject,
    mut v___y_4503_: *mut crate::leanh::LeanObject,
    mut v___y_4504_: *mut crate::leanh::LeanObject,
    mut v___y_4505_: *mut crate::leanh::LeanObject,
    mut v___y_4506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4507_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(v_k_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v_b_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
    crate::leanh::lean_dec(v___y_4505_);
    crate::leanh::lean_dec_ref(v___y_4504_);
    crate::leanh::lean_dec(v___y_4503_);
    crate::leanh::lean_dec_ref(v___y_4502_);
    crate::leanh::lean_dec(v___y_4500_);
    crate::leanh::lean_dec_ref(v___y_4499_);
    crate::leanh::lean_dec(v___y_4498_);
    return v_res_4507_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(
    mut v_name_4508_: *mut crate::leanh::LeanObject,
    mut v_bi_4509_: u8,
    mut v_type_4510_: *mut crate::leanh::LeanObject,
    mut v_k_4511_: *mut crate::leanh::LeanObject,
    mut v_kind_4512_: u8,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4515_);
                crate::leanh::lean_inc_ref(v___y_4514_);
                crate::leanh::lean_inc(v___y_4513_);
                v___f_4521_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                crate::leanh::lean_closure_set(v___f_4521_, 0, v_k_4511_);
                crate::leanh::lean_closure_set(v___f_4521_, 1, v___y_4513_);
                crate::leanh::lean_closure_set(v___f_4521_, 2, v___y_4514_);
                crate::leanh::lean_closure_set(v___f_4521_, 3, v___y_4515_);
                v___x_4522_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4508_,
                    v_bi_4509_,
                    v_type_4510_,
                    v___f_4521_,
                    v_kind_4512_,
                    v___y_4516_,
                    v___y_4517_,
                    v___y_4518_,
                    v___y_4519_,
                );
                if crate::leanh::lean_obj_tag(v___x_4522_) == 0 {
                    return v___x_4522_;
                } else {
                    v_a_4523_ = crate::leanh::lean_ctor_get(v___x_4522_, 0);
                    v_isSharedCheck_4530_ = (!crate::leanh::lean_is_exclusive(v___x_4522_)) as u8;
                    if v_isSharedCheck_4530_ == 0 {
                        v___x_4525_ = v___x_4522_;
                        v_isShared_4526_ = v_isSharedCheck_4530_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4523_);
                        crate::leanh::lean_dec(v___x_4522_);
                        v___x_4525_ = crate::leanh::lean_box(0);
                        v_isShared_4526_ = v_isSharedCheck_4530_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4526_ == 0 {
                    v___x_4528_ = v___x_4525_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4529_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_a_4523_);
                    v___x_4528_ = v_reuseFailAlloc_4529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(
    mut v_name_4531_: *mut crate::leanh::LeanObject,
    mut v_bi_4532_: *mut crate::leanh::LeanObject,
    mut v_type_4533_: *mut crate::leanh::LeanObject,
    mut v_k_4534_: *mut crate::leanh::LeanObject,
    mut v_kind_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4544_: u8 = 0;
    let mut v_kind_boxed_4545_: u8 = 0;
    let mut v_res_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4544_ = (crate::leanh::lean_unbox(v_bi_4532_) as u8);
    v_kind_boxed_4545_ = (crate::leanh::lean_unbox(v_kind_4535_) as u8);
    v_res_4546_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_4531_, v_bi_boxed_4544_, v_type_4533_, v_k_4534_, v_kind_boxed_4545_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
    crate::leanh::lean_dec(v___y_4542_);
    crate::leanh::lean_dec_ref(v___y_4541_);
    crate::leanh::lean_dec(v___y_4540_);
    crate::leanh::lean_dec_ref(v___y_4539_);
    crate::leanh::lean_dec(v___y_4538_);
    crate::leanh::lean_dec_ref(v___y_4537_);
    crate::leanh::lean_dec(v___y_4536_);
    return v_res_4546_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(
    mut v_name_4547_: *mut crate::leanh::LeanObject,
    mut v_type_4548_: *mut crate::leanh::LeanObject,
    mut v_k_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
    mut v___y_4552_: *mut crate::leanh::LeanObject,
    mut v___y_4553_: *mut crate::leanh::LeanObject,
    mut v___y_4554_: *mut crate::leanh::LeanObject,
    mut v___y_4555_: *mut crate::leanh::LeanObject,
    mut v___y_4556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = 0;
    v___x_4559_ = 0;
    v___x_4560_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_4547_, v___x_4558_, v_type_4548_, v_k_4549_, v___x_4559_, v___y_4550_, v___y_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
    return v___x_4560_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(
    mut v_name_4561_: *mut crate::leanh::LeanObject,
    mut v_type_4562_: *mut crate::leanh::LeanObject,
    mut v_k_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4572_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(
        v_name_4561_,
        v_type_4562_,
        v_k_4563_,
        v___y_4564_,
        v___y_4565_,
        v___y_4566_,
        v___y_4567_,
        v___y_4568_,
        v___y_4569_,
        v___y_4570_,
    );
    crate::leanh::lean_dec(v___y_4570_);
    crate::leanh::lean_dec_ref(v___y_4569_);
    crate::leanh::lean_dec(v___y_4568_);
    crate::leanh::lean_dec_ref(v___y_4567_);
    crate::leanh::lean_dec(v___y_4566_);
    crate::leanh::lean_dec_ref(v___y_4565_);
    crate::leanh::lean_dec(v___y_4564_);
    return v_res_4572_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__13() -> *mut crate::leanh::LeanObject {
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4599_ = crate::leanh::lean_box(0);
    v___x_4600_ = l_Lean_Meta_Grind_simpForall___closed__12;
    v___x_4601_ = l_Lean_mkConst(v___x_4600_, v___x_4599_);
    return v___x_4601_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__16() -> *mut crate::leanh::LeanObject {
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4607_ = crate::leanh::lean_box(0);
    v___x_4608_ = l_Lean_Meta_Grind_simpForall___closed__15;
    v___x_4609_ = l_Lean_mkConst(v___x_4608_, v___x_4607_);
    return v___x_4609_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = crate::leanh::lean_box(0);
    v___x_4621_ = l_Lean_Meta_Grind_simpForall___closed__20;
    v___x_4622_ = l_Lean_mkConst(v___x_4621_, v___x_4620_);
    return v___x_4622_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__24() -> *mut crate::leanh::LeanObject {
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4628_ = crate::leanh::lean_box(0);
    v___x_4629_ = l_Lean_Meta_Grind_simpForall___closed__23;
    v___x_4630_ = l_Lean_mkConst(v___x_4629_, v___x_4628_);
    return v___x_4630_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__27() -> *mut crate::leanh::LeanObject {
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4636_ = crate::leanh::lean_box(0);
    v___x_4637_ = l_Lean_Meta_Grind_simpForall___closed__26;
    v___x_4638_ = l_Lean_mkConst(v___x_4637_, v___x_4636_);
    return v___x_4638_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__30() -> *mut crate::leanh::LeanObject {
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4644_ = crate::leanh::lean_box(0);
    v___x_4645_ = l_Lean_Meta_Grind_simpForall___closed__29;
    v___x_4646_ = l_Lean_mkConst(v___x_4645_, v___x_4644_);
    return v___x_4646_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__33() -> *mut crate::leanh::LeanObject {
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4651_ = crate::leanh::lean_box(0);
    v___x_4652_ = l_Lean_Meta_Grind_simpForall___closed__32;
    v___x_4653_ = l_Lean_mkConst(v___x_4652_, v___x_4651_);
    return v___x_4653_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__36() -> *mut crate::leanh::LeanObject {
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4659_ = crate::leanh::lean_box(0);
    v___x_4660_ = l_Lean_Meta_Grind_simpForall___closed__35;
    v___x_4661_ = l_Lean_mkConst(v___x_4660_, v___x_4659_);
    return v___x_4661_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__37() -> *mut crate::leanh::LeanObject {
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4662_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4663_ = l_Lean_Level_ofNat(v___x_4662_);
    return v___x_4663_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__38() -> *mut crate::leanh::LeanObject {
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4664_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__37),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__37_once),
        _init_l_Lean_Meta_Grind_simpForall___closed__37,
    );
    v___x_4665_ = l_Lean_mkSort(v___x_4664_);
    return v___x_4665_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpForall___closed__41() -> *mut crate::leanh::LeanObject {
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4669_ = crate::leanh::lean_box(0);
    v___x_4670_ = l_Lean_Meta_Grind_simpForall___closed__40;
    v___x_4671_ = l_Lean_mkConst(v___x_4670_, v___x_4669_);
    return v___x_4671_;
}
pub unsafe fn l_Lean_Meta_Grind_simpForall(
    mut v_e_4672_: *mut crate::leanh::LeanObject,
    mut v_a_4673_: *mut crate::leanh::LeanObject,
    mut v_a_4674_: *mut crate::leanh::LeanObject,
    mut v_a_4675_: *mut crate::leanh::LeanObject,
    mut v_a_4676_: *mut crate::leanh::LeanObject,
    mut v_a_4677_: *mut crate::leanh::LeanObject,
    mut v_a_4678_: *mut crate::leanh::LeanObject,
    mut v_a_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4687_: u8 = 0;
    let mut v___y_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4696_: u8 = 0;
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: u8 = 0;
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: u8 = 0;
    let mut v_pRaw_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_qRaw_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4714_: u8 = 0;
    let mut v_expr_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4727_: u8 = 0;
    let mut v_a_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4731_: u8 = 0;
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4735_: u8 = 0;
    let mut v_pRaw_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pRaw_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4742_: u8 = 0;
    let mut v_snd_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4747_: u8 = 0;
    let mut v_fst_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4752_: u8 = 0;
    let mut v_p_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: u8 = 0;
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4765_: u8 = 0;
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4790_: u8 = 0;
    let mut v_a_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4794_: u8 = 0;
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4798_: u8 = 0;
    let mut v_a_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4802_: u8 = 0;
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v_isSharedCheck_4809_: u8 = 0;
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4814_: u8 = 0;
    let mut v_snd_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v_fst_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4824_: u8 = 0;
    let mut v_p_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_00_u03b2_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4837_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4862_: u8 = 0;
    let mut v_a_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4866_: u8 = 0;
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4870_: u8 = 0;
    let mut v_a_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4874_: u8 = 0;
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4878_: u8 = 0;
    let mut v_isSharedCheck_4879_: u8 = 0;
    let mut v_isSharedCheck_4880_: u8 = 0;
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: u8 = 0;
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: u8 = 0;
    let mut v___x_4896_: u8 = 0;
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: u8 = 0;
    let mut v___y_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4905_: u8 = 0;
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4916_: u8 = 0;
    let mut v_a_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4920_: u8 = 0;
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4924_: u8 = 0;
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: u8 = 0;
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: u8 = 0;
    let mut v_binderName_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4933_: u8 = 0;
    let mut v_a_4935_: u8 = 0;
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4941_: u8 = 0;
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4959_: u8 = 0;
    let mut v_a_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4963_: u8 = 0;
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4967_: u8 = 0;
    let mut v___x_4968_: u8 = 0;
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: u8 = 0;
    let mut v_a_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4975_: u8 = 0;
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4979_: u8 = 0;
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: u8 = 0;
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4993_: u8 = 0;
    let mut v___x_4994_: u8 = 0;
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5004_: u8 = 0;
    let mut v_a_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5008_: u8 = 0;
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5012_: u8 = 0;
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5017_: u8 = 0;
    let mut v___x_5018_: u8 = 0;
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5028_: u8 = 0;
    let mut v_a_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_a_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5049_: u8 = 0;
    let mut v___x_5050_: u8 = 0;
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5059_: u8 = 0;
    let mut v_a_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5067_: u8 = 0;
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5072_: u8 = 0;
    let mut v___x_5073_: u8 = 0;
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5083_: u8 = 0;
    let mut v_a_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5091_: u8 = 0;
    let mut v_a_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5095_: u8 = 0;
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5099_: u8 = 0;
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: u8 = 0;
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5113_: u8 = 0;
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5124_: u8 = 0;
    let mut v_a_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5128_: u8 = 0;
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5132_: u8 = 0;
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5142_: u8 = 0;
    let mut v___x_5143_: u8 = 0;
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5153_: u8 = 0;
    let mut v_a_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5157_: u8 = 0;
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5161_: u8 = 0;
    let mut v_a_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5165_: u8 = 0;
    let mut v___x_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5169_: u8 = 0;
    let mut v_a_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5173_: u8 = 0;
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5177_: u8 = 0;
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_4672_) == 7 {
                    v_binderName_4684_ = crate::leanh::lean_ctor_get(v_e_4672_, 0);
                    crate::leanh::lean_inc(v_binderName_4684_);
                    v_binderType_4685_ = crate::leanh::lean_ctor_get(v_e_4672_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_4685_);
                    v_body_4686_ = crate::leanh::lean_ctor_get(v_e_4672_, 2);
                    crate::leanh::lean_inc_ref(v_body_4686_);
                    v_binderInfo_4687_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_4672_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_4672_, 3);
                    v___x_4896_ = l_Lean_Expr_hasLooseBVars(v_body_4686_);
                    if v___x_4896_ == 0 {
                        crate::leanh::lean_inc_ref(v_binderType_4685_);
                        v___x_4897_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                            v_binderType_4685_,
                            v_a_4677_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4897_) == 0 {
                            v_a_4898_ = crate::leanh::lean_ctor_get(v___x_4897_, 0);
                            crate::leanh::lean_inc(v_a_4898_);
                            crate::leanh::lean_dec_ref_known(v___x_4897_, 1);
                            v___x_4899_ = 1;
                            v___x_4925_ = l_Lean_Expr_cleanupAnnotations(v_a_4898_);
                            v___x_4926_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
                            v___x_4927_ = l_Lean_Expr_isConstOf(v___x_4925_, v___x_4926_);
                            if v___x_4927_ == 0 {
                                v___x_4928_ = l_Lean_Meta_Grind_simpForall___closed__12;
                                v___x_4929_ = l_Lean_Expr_isConstOf(v___x_4925_, v___x_4928_);
                                crate::leanh::lean_dec_ref(v___x_4925_);
                                if v___x_4929_ == 0 {
                                    if crate::leanh::lean_obj_tag(v_binderType_4685_) == 7 {
                                        v_binderName_4930_ =
                                            crate::leanh::lean_ctor_get(v_binderType_4685_, 0);
                                        v_binderType_4931_ =
                                            crate::leanh::lean_ctor_get(v_binderType_4685_, 1);
                                        v_body_4932_ =
                                            crate::leanh::lean_ctor_get(v_binderType_4685_, 2);
                                        v_binderInfo_4933_ = crate::leanh::lean_ctor_get_uint8(
                                            v_binderType_4685_,
                                            (core::mem::size_of::<*mut crate::leanh::LeanObject>()
                                                * 3
                                                + 8)
                                                as u32,
                                        );
                                        v___x_4968_ = l_Lean_Expr_hasLooseBVars(v_body_4932_);
                                        if v___x_4968_ == 0 {
                                            v_a_4935_ = v___x_4968_;
                                            state = 37;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc_ref(v_binderType_4685_);
                                            v___x_4969_ = l_Lean_Meta_isProp(
                                                v_binderType_4685_,
                                                v_a_4676_,
                                                v_a_4677_,
                                                v_a_4678_,
                                                v_a_4679_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_4969_) == 0 {
                                                v_a_4970_ =
                                                    crate::leanh::lean_ctor_get(v___x_4969_, 0);
                                                crate::leanh::lean_inc(v_a_4970_);
                                                crate::leanh::lean_dec_ref_known(v___x_4969_, 1);
                                                v___x_4971_ =
                                                    (crate::leanh::lean_unbox(v_a_4970_) as u8);
                                                crate::leanh::lean_dec(v_a_4970_);
                                                v_a_4935_ = v___x_4971_;
                                                state = 37;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref_known(
                                                    v_binderType_4685_,
                                                    3,
                                                );
                                                crate::leanh::lean_dec_ref(v_body_4686_);
                                                crate::leanh::lean_dec(v_binderName_4684_);
                                                v_a_4972_ =
                                                    crate::leanh::lean_ctor_get(v___x_4969_, 0);
                                                v_isSharedCheck_4979_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4969_))
                                                        as u8;
                                                if v_isSharedCheck_4979_ == 0 {
                                                    v___x_4974_ = v___x_4969_;
                                                    v_isShared_4975_ = v_isSharedCheck_4979_;
                                                    state = 42;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4972_);
                                                    crate::leanh::lean_dec(v___x_4969_);
                                                    v___x_4974_ = crate::leanh::lean_box(0);
                                                    v_isShared_4975_ = v_isSharedCheck_4979_;
                                                    state = 42;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_inc_ref(v_body_4686_);
                                        v___x_4980_ =
                                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                v_body_4686_,
                                                v_a_4677_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_4980_) == 0 {
                                            v_a_4981_ = crate::leanh::lean_ctor_get(v___x_4980_, 0);
                                            crate::leanh::lean_inc(v_a_4981_);
                                            crate::leanh::lean_dec_ref_known(v___x_4980_, 1);
                                            v___x_4982_ = l_Lean_Expr_cleanupAnnotations(v_a_4981_);
                                            v___x_4983_ =
                                                l_Lean_Expr_isConstOf(v___x_4982_, v___x_4926_);
                                            if v___x_4983_ == 0 {
                                                v___x_4984_ =
                                                    l_Lean_Expr_isConstOf(v___x_4982_, v___x_4928_);
                                                crate::leanh::lean_dec_ref(v___x_4982_);
                                                if v___x_4984_ == 0 {
                                                    crate::leanh::lean_inc_ref(v_binderType_4685_);
                                                    v___x_4985_ = l_Lean_Meta_isProp(
                                                        v_binderType_4685_,
                                                        v_a_4676_,
                                                        v_a_4677_,
                                                        v_a_4678_,
                                                        v_a_4679_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_4985_) == 0
                                                    {
                                                        v_a_4986_ = crate::leanh::lean_ctor_get(
                                                            v___x_4985_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_4986_);
                                                        v___x_4987_ =
                                                            (crate::leanh::lean_unbox(v_a_4986_)
                                                                as u8);
                                                        crate::leanh::lean_dec(v_a_4986_);
                                                        if v___x_4987_ == 0 {
                                                            v___y_4901_ = v___x_4985_;
                                                            state = 32;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_4985_,
                                                                1,
                                                            );
                                                            crate::leanh::lean_inc_ref(
                                                                v_body_4686_,
                                                            );
                                                            crate::leanh::lean_inc_ref(
                                                                v_binderType_4685_,
                                                            );
                                                            v___x_4988_ = l_Lean_Meta_isExprDefEq(
                                                                v_binderType_4685_,
                                                                v_body_4686_,
                                                                v_a_4676_,
                                                                v_a_4677_,
                                                                v_a_4678_,
                                                                v_a_4679_,
                                                            );
                                                            v___y_4901_ = v___x_4988_;
                                                            state = 32;
                                                            continue;
                                                        }
                                                    } else {
                                                        v___y_4901_ = v___x_4985_;
                                                        state = 32;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_inc_ref(v_binderType_4685_);
                                                    v___x_4989_ = l_Lean_Meta_isProp(
                                                        v_binderType_4685_,
                                                        v_a_4676_,
                                                        v_a_4677_,
                                                        v_a_4678_,
                                                        v_a_4679_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_4989_) == 0
                                                    {
                                                        v_a_4990_ = crate::leanh::lean_ctor_get(
                                                            v___x_4989_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5004_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_4989_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_5004_ == 0 {
                                                            v___x_4992_ = v___x_4989_;
                                                            v_isShared_4993_ =
                                                                v_isSharedCheck_5004_;
                                                            state = 44;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_4990_);
                                                            crate::leanh::lean_dec(v___x_4989_);
                                                            v___x_4992_ = crate::leanh::lean_box(0);
                                                            v_isShared_4993_ =
                                                                v_isSharedCheck_5004_;
                                                            state = 44;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_body_4686_);
                                                        crate::leanh::lean_dec_ref(
                                                            v_binderType_4685_,
                                                        );
                                                        crate::leanh::lean_dec(v_binderName_4684_);
                                                        v_a_5005_ = crate::leanh::lean_ctor_get(
                                                            v___x_4989_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_5012_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_4989_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_5012_ == 0 {
                                                            v___x_5007_ = v___x_4989_;
                                                            v_isShared_5008_ =
                                                                v_isSharedCheck_5012_;
                                                            state = 46;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_5005_);
                                                            crate::leanh::lean_dec(v___x_4989_);
                                                            v___x_5007_ = crate::leanh::lean_box(0);
                                                            v_isShared_5008_ =
                                                                v_isSharedCheck_5012_;
                                                            state = 46;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_4982_);
                                                crate::leanh::lean_inc_ref(v_binderType_4685_);
                                                v___x_5013_ = l_Lean_Meta_isProp(
                                                    v_binderType_4685_,
                                                    v_a_4676_,
                                                    v_a_4677_,
                                                    v_a_4678_,
                                                    v_a_4679_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_5013_) == 0 {
                                                    v_a_5014_ =
                                                        crate::leanh::lean_ctor_get(v___x_5013_, 0);
                                                    v_isSharedCheck_5028_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5013_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5028_ == 0 {
                                                        v___x_5016_ = v___x_5013_;
                                                        v_isShared_5017_ = v_isSharedCheck_5028_;
                                                        state = 48;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5014_);
                                                        crate::leanh::lean_dec(v___x_5013_);
                                                        v___x_5016_ = crate::leanh::lean_box(0);
                                                        v_isShared_5017_ = v_isSharedCheck_5028_;
                                                        state = 48;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_body_4686_);
                                                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                                                    crate::leanh::lean_dec(v_binderName_4684_);
                                                    v_a_5029_ =
                                                        crate::leanh::lean_ctor_get(v___x_5013_, 0);
                                                    v_isSharedCheck_5036_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5013_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5036_ == 0 {
                                                        v___x_5031_ = v___x_5013_;
                                                        v_isShared_5032_ = v_isSharedCheck_5036_;
                                                        state = 50;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5029_);
                                                        crate::leanh::lean_dec(v___x_5013_);
                                                        v___x_5031_ = crate::leanh::lean_box(0);
                                                        v_isShared_5032_ = v_isSharedCheck_5036_;
                                                        state = 50;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v_body_4686_);
                                            crate::leanh::lean_dec_ref(v_binderType_4685_);
                                            crate::leanh::lean_dec(v_binderName_4684_);
                                            v_a_5037_ = crate::leanh::lean_ctor_get(v___x_4980_, 0);
                                            v_isSharedCheck_5044_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_4980_))
                                                    as u8;
                                            if v_isSharedCheck_5044_ == 0 {
                                                v___x_5039_ = v___x_4980_;
                                                v_isShared_5040_ = v_isSharedCheck_5044_;
                                                state = 52;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5037_);
                                                crate::leanh::lean_dec(v___x_4980_);
                                                v___x_5039_ = crate::leanh::lean_box(0);
                                                v_isShared_5040_ = v_isSharedCheck_5044_;
                                                state = 52;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_inc_ref(v_body_4686_);
                                    v___x_5045_ = l_Lean_Meta_isProp(
                                        v_body_4686_,
                                        v_a_4676_,
                                        v_a_4677_,
                                        v_a_4678_,
                                        v_a_4679_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5045_) == 0 {
                                        v_a_5046_ = crate::leanh::lean_ctor_get(v___x_5045_, 0);
                                        v_isSharedCheck_5059_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5045_)) as u8;
                                        if v_isSharedCheck_5059_ == 0 {
                                            v___x_5048_ = v___x_5045_;
                                            v_isShared_5049_ = v_isSharedCheck_5059_;
                                            state = 54;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5046_);
                                            crate::leanh::lean_dec(v___x_5045_);
                                            v___x_5048_ = crate::leanh::lean_box(0);
                                            v_isShared_5049_ = v_isSharedCheck_5059_;
                                            state = 54;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_body_4686_);
                                        crate::leanh::lean_dec_ref(v_binderType_4685_);
                                        crate::leanh::lean_dec(v_binderName_4684_);
                                        v_a_5060_ = crate::leanh::lean_ctor_get(v___x_5045_, 0);
                                        v_isSharedCheck_5067_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5045_)) as u8;
                                        if v_isSharedCheck_5067_ == 0 {
                                            v___x_5062_ = v___x_5045_;
                                            v_isShared_5063_ = v_isSharedCheck_5067_;
                                            state = 56;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5060_);
                                            crate::leanh::lean_dec(v___x_5045_);
                                            v___x_5062_ = crate::leanh::lean_box(0);
                                            v_isShared_5063_ = v_isSharedCheck_5067_;
                                            state = 56;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_4925_);
                                crate::leanh::lean_inc_ref(v_body_4686_);
                                v___x_5068_ = l_Lean_Meta_isProp(
                                    v_body_4686_,
                                    v_a_4676_,
                                    v_a_4677_,
                                    v_a_4678_,
                                    v_a_4679_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5068_) == 0 {
                                    v_a_5069_ = crate::leanh::lean_ctor_get(v___x_5068_, 0);
                                    v_isSharedCheck_5083_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5068_)) as u8;
                                    if v_isSharedCheck_5083_ == 0 {
                                        v___x_5071_ = v___x_5068_;
                                        v_isShared_5072_ = v_isSharedCheck_5083_;
                                        state = 58;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5069_);
                                        crate::leanh::lean_dec(v___x_5068_);
                                        v___x_5071_ = crate::leanh::lean_box(0);
                                        v_isShared_5072_ = v_isSharedCheck_5083_;
                                        state = 58;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_body_4686_);
                                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                                    crate::leanh::lean_dec(v_binderName_4684_);
                                    v_a_5084_ = crate::leanh::lean_ctor_get(v___x_5068_, 0);
                                    v_isSharedCheck_5091_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5068_)) as u8;
                                    if v_isSharedCheck_5091_ == 0 {
                                        v___x_5086_ = v___x_5068_;
                                        v_isShared_5087_ = v_isSharedCheck_5091_;
                                        state = 60;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5084_);
                                        crate::leanh::lean_dec(v___x_5068_);
                                        v___x_5086_ = crate::leanh::lean_box(0);
                                        v_isShared_5087_ = v_isSharedCheck_5091_;
                                        state = 60;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_4686_);
                            crate::leanh::lean_dec_ref(v_binderType_4685_);
                            crate::leanh::lean_dec(v_binderName_4684_);
                            v_a_5092_ = crate::leanh::lean_ctor_get(v___x_4897_, 0);
                            v_isSharedCheck_5099_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4897_)) as u8;
                            if v_isSharedCheck_5099_ == 0 {
                                v___x_5094_ = v___x_4897_;
                                v_isShared_5095_ = v_isSharedCheck_5099_;
                                state = 62;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5092_);
                                crate::leanh::lean_dec(v___x_4897_);
                                v___x_5094_ = crate::leanh::lean_box(0);
                                v_isShared_5095_ = v_isSharedCheck_5099_;
                                state = 62;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v_binderType_4685_);
                        v___x_5100_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                            v_binderType_4685_,
                            v_a_4677_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5100_) == 0 {
                            v_a_5101_ = crate::leanh::lean_ctor_get(v___x_5100_, 0);
                            crate::leanh::lean_inc(v_a_5101_);
                            crate::leanh::lean_dec_ref_known(v___x_5100_, 1);
                            v___x_5102_ = l_Lean_Expr_cleanupAnnotations(v_a_5101_);
                            v___x_5103_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
                            v___x_5104_ = l_Lean_Expr_isConstOf(v___x_5102_, v___x_5103_);
                            if v___x_5104_ == 0 {
                                v___x_5105_ = l_Lean_Meta_Grind_simpForall___closed__12;
                                v___x_5106_ = l_Lean_Expr_isConstOf(v___x_5102_, v___x_5105_);
                                crate::leanh::lean_dec_ref(v___x_5102_);
                                if v___x_5106_ == 0 {
                                    v___y_4885_ = v_a_4673_;
                                    v___y_4886_ = v_a_4674_;
                                    v___y_4887_ = v_a_4675_;
                                    v___y_4888_ = v_a_4676_;
                                    v___y_4889_ = v_a_4677_;
                                    v___y_4890_ = v_a_4678_;
                                    v___y_4891_ = v_a_4679_;
                                    state = 31;
                                    continue;
                                } else {
                                    v___x_5107_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpForall___closed__33
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpForall___closed__33_once
                                        ),
                                        _init_l_Lean_Meta_Grind_simpForall___closed__33,
                                    );
                                    v___x_5108_ = lean_expr_instantiate1(v_body_4686_, v___x_5107_);
                                    crate::leanh::lean_inc_ref(v___x_5108_);
                                    v___x_5109_ = l_Lean_Meta_isProp(
                                        v___x_5108_,
                                        v_a_4676_,
                                        v_a_4677_,
                                        v_a_4678_,
                                        v_a_4679_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5109_) == 0 {
                                        v_a_5110_ = crate::leanh::lean_ctor_get(v___x_5109_, 0);
                                        v_isSharedCheck_5124_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5109_)) as u8;
                                        if v_isSharedCheck_5124_ == 0 {
                                            v___x_5112_ = v___x_5109_;
                                            v_isShared_5113_ = v_isSharedCheck_5124_;
                                            state = 64;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5110_);
                                            crate::leanh::lean_dec(v___x_5109_);
                                            v___x_5112_ = crate::leanh::lean_box(0);
                                            v_isShared_5113_ = v_isSharedCheck_5124_;
                                            state = 64;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_5108_);
                                        crate::leanh::lean_dec_ref(v_body_4686_);
                                        crate::leanh::lean_dec_ref(v_binderType_4685_);
                                        crate::leanh::lean_dec(v_binderName_4684_);
                                        v_a_5125_ = crate::leanh::lean_ctor_get(v___x_5109_, 0);
                                        v_isSharedCheck_5132_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5109_)) as u8;
                                        if v_isSharedCheck_5132_ == 0 {
                                            v___x_5127_ = v___x_5109_;
                                            v_isShared_5128_ = v_isSharedCheck_5132_;
                                            state = 66;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5125_);
                                            crate::leanh::lean_dec(v___x_5109_);
                                            v___x_5127_ = crate::leanh::lean_box(0);
                                            v_isShared_5128_ = v_isSharedCheck_5132_;
                                            state = 66;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5102_);
                                crate::leanh::lean_inc_ref(v_body_4686_);
                                crate::leanh::lean_inc_ref(v_binderType_4685_);
                                crate::leanh::lean_inc(v_binderName_4684_);
                                v___x_5133_ = l_Lean_mkLambda(
                                    v_binderName_4684_,
                                    v_binderInfo_4687_,
                                    v_binderType_4685_,
                                    v_body_4686_,
                                );
                                crate::leanh::lean_inc(v_a_4679_);
                                crate::leanh::lean_inc_ref(v_a_4678_);
                                crate::leanh::lean_inc(v_a_4677_);
                                crate::leanh::lean_inc_ref(v_a_4676_);
                                crate::leanh::lean_inc_ref(v___x_5133_);
                                v___x_5134_ = lean_infer_type(
                                    v___x_5133_,
                                    v_a_4676_,
                                    v_a_4677_,
                                    v_a_4678_,
                                    v_a_4679_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_5134_) == 0 {
                                    v_a_5135_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                                    crate::leanh::lean_inc(v_a_5135_);
                                    crate::leanh::lean_dec_ref_known(v___x_5134_, 1);
                                    v___x_5136_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpForall___closed__38
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpForall___closed__38_once
                                        ),
                                        _init_l_Lean_Meta_Grind_simpForall___closed__38,
                                    );
                                    crate::leanh::lean_inc_ref(v_binderType_4685_);
                                    crate::leanh::lean_inc(v_binderName_4684_);
                                    v___x_5137_ = l_Lean_mkForall(
                                        v_binderName_4684_,
                                        v_binderInfo_4687_,
                                        v_binderType_4685_,
                                        v___x_5136_,
                                    );
                                    v___x_5138_ = l_Lean_Meta_isExprDefEq(
                                        v_a_5135_,
                                        v___x_5137_,
                                        v_a_4676_,
                                        v_a_4677_,
                                        v_a_4678_,
                                        v_a_4679_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5138_) == 0 {
                                        v_a_5139_ = crate::leanh::lean_ctor_get(v___x_5138_, 0);
                                        v_isSharedCheck_5153_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5138_)) as u8;
                                        if v_isSharedCheck_5153_ == 0 {
                                            v___x_5141_ = v___x_5138_;
                                            v_isShared_5142_ = v_isSharedCheck_5153_;
                                            state = 68;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5139_);
                                            crate::leanh::lean_dec(v___x_5138_);
                                            v___x_5141_ = crate::leanh::lean_box(0);
                                            v_isShared_5142_ = v_isSharedCheck_5153_;
                                            state = 68;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_5133_);
                                        crate::leanh::lean_dec_ref(v_body_4686_);
                                        crate::leanh::lean_dec_ref(v_binderType_4685_);
                                        crate::leanh::lean_dec(v_binderName_4684_);
                                        v_a_5154_ = crate::leanh::lean_ctor_get(v___x_5138_, 0);
                                        v_isSharedCheck_5161_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5138_)) as u8;
                                        if v_isSharedCheck_5161_ == 0 {
                                            v___x_5156_ = v___x_5138_;
                                            v_isShared_5157_ = v_isSharedCheck_5161_;
                                            state = 70;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5154_);
                                            crate::leanh::lean_dec(v___x_5138_);
                                            v___x_5156_ = crate::leanh::lean_box(0);
                                            v_isShared_5157_ = v_isSharedCheck_5161_;
                                            state = 70;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_5133_);
                                    crate::leanh::lean_dec_ref(v_body_4686_);
                                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                                    crate::leanh::lean_dec(v_binderName_4684_);
                                    v_a_5162_ = crate::leanh::lean_ctor_get(v___x_5134_, 0);
                                    v_isSharedCheck_5169_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5134_)) as u8;
                                    if v_isSharedCheck_5169_ == 0 {
                                        v___x_5164_ = v___x_5134_;
                                        v_isShared_5165_ = v_isSharedCheck_5169_;
                                        state = 72;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5162_);
                                        crate::leanh::lean_dec(v___x_5134_);
                                        v___x_5164_ = crate::leanh::lean_box(0);
                                        v_isShared_5165_ = v_isSharedCheck_5169_;
                                        state = 72;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_4686_);
                            crate::leanh::lean_dec_ref(v_binderType_4685_);
                            crate::leanh::lean_dec(v_binderName_4684_);
                            v_a_5170_ = crate::leanh::lean_ctor_get(v___x_5100_, 0);
                            v_isSharedCheck_5177_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5100_)) as u8;
                            if v_isSharedCheck_5177_ == 0 {
                                v___x_5172_ = v___x_5100_;
                                v_isShared_5173_ = v_isSharedCheck_5177_;
                                state = 74;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5170_);
                                crate::leanh::lean_dec(v___x_5100_);
                                v___x_5172_ = crate::leanh::lean_box(0);
                                v_isShared_5173_ = v_isSharedCheck_5177_;
                                state = 74;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4672_);
                    v___x_5178_ = l_Lean_Meta_Grind_simpForall___closed__0;
                    v___x_5179_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5179_, 0, v___x_5178_);
                    return v___x_5179_;
                }
            }
            1 => {
                v___x_4682_ = l_Lean_Meta_Grind_simpForall___closed__0;
                v___x_4683_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4683_, 0, v___x_4682_);
                return v___x_4683_;
            }
            2 => {
                if v___y_4696_ == 0 {
                    crate::leanh::lean_dec_ref(v_body_4686_);
                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    state = 1;
                    continue;
                } else {
                    v___x_4697_ = l_Lean_Expr_appFn_x21(v_body_4686_);
                    v___x_4698_ = l_Lean_Expr_appFn_x21(v___x_4697_);
                    if crate::leanh::lean_obj_tag(v___x_4698_) == 4 {
                        v_declName_4699_ = crate::leanh::lean_ctor_get(v___x_4698_, 0);
                        crate::leanh::lean_inc(v_declName_4699_);
                        crate::leanh::lean_dec_ref_known(v___x_4698_, 2);
                        v___x_4700_ = l_Lean_Meta_Grind_simpForall___closed__2;
                        v___x_4701_ = lean_name_eq(v_declName_4699_, v___x_4700_);
                        if v___x_4701_ == 0 {
                            v___x_4702_ = l_Lean_Meta_Grind_simpForall___closed__4;
                            v___x_4703_ = lean_name_eq(v_declName_4699_, v___x_4702_);
                            crate::leanh::lean_dec(v_declName_4699_);
                            if v___x_4703_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4697_);
                                crate::leanh::lean_dec_ref(v_body_4686_);
                                crate::leanh::lean_dec_ref(v_binderType_4685_);
                                crate::leanh::lean_dec(v_binderName_4684_);
                                state = 1;
                                continue;
                            } else {
                                v_pRaw_4704_ = l_Lean_Expr_appArg_x21(v___x_4697_);
                                crate::leanh::lean_dec_ref(v___x_4697_);
                                v_qRaw_4705_ = l_Lean_Expr_appArg_x21(v_body_4686_);
                                crate::leanh::lean_dec_ref(v_body_4686_);
                                crate::leanh::lean_inc_ref(v_pRaw_4704_);
                                crate::leanh::lean_inc_ref_n(v_binderType_4685_, 5);
                                crate::leanh::lean_inc_n(v_binderName_4684_, 3);
                                v_p_4706_ = l_Lean_mkLambda(
                                    v_binderName_4684_,
                                    v_binderInfo_4687_,
                                    v_binderType_4685_,
                                    v_pRaw_4704_,
                                );
                                crate::leanh::lean_inc_ref(v_qRaw_4705_);
                                v_q_4707_ = l_Lean_mkLambda(
                                    v_binderName_4684_,
                                    v_binderInfo_4687_,
                                    v_binderType_4685_,
                                    v_qRaw_4705_,
                                );
                                v___x_4708_ = l_Lean_mkForall(
                                    v_binderName_4684_,
                                    v_binderInfo_4687_,
                                    v_binderType_4685_,
                                    v_pRaw_4704_,
                                );
                                v___x_4709_ = l_Lean_mkForall(
                                    v_binderName_4684_,
                                    v_binderInfo_4687_,
                                    v_binderType_4685_,
                                    v_qRaw_4705_,
                                );
                                v___x_4710_ = l_Lean_Meta_getLevel(
                                    v_binderType_4685_,
                                    v___y_4694_,
                                    v___y_4691_,
                                    v___y_4690_,
                                    v___y_4695_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4710_) == 0 {
                                    v_a_4711_ = crate::leanh::lean_ctor_get(v___x_4710_, 0);
                                    v_isSharedCheck_4727_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4710_)) as u8;
                                    if v_isSharedCheck_4727_ == 0 {
                                        v___x_4713_ = v___x_4710_;
                                        v_isShared_4714_ = v_isSharedCheck_4727_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4711_);
                                        crate::leanh::lean_dec(v___x_4710_);
                                        v___x_4713_ = crate::leanh::lean_box(0);
                                        v_isShared_4714_ = v_isSharedCheck_4727_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4709_);
                                    crate::leanh::lean_dec_ref(v___x_4708_);
                                    crate::leanh::lean_dec_ref(v_q_4707_);
                                    crate::leanh::lean_dec_ref(v_p_4706_);
                                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                                    v_a_4728_ = crate::leanh::lean_ctor_get(v___x_4710_, 0);
                                    v_isSharedCheck_4735_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4710_)) as u8;
                                    if v_isSharedCheck_4735_ == 0 {
                                        v___x_4730_ = v___x_4710_;
                                        v_isShared_4731_ = v_isSharedCheck_4735_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4728_);
                                        crate::leanh::lean_dec(v___x_4710_);
                                        v___x_4730_ = crate::leanh::lean_box(0);
                                        v_isShared_4731_ = v_isSharedCheck_4735_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_4699_);
                            v_pRaw_4736_ = l_Lean_Expr_appArg_x21(v___x_4697_);
                            crate::leanh::lean_dec_ref(v___x_4697_);
                            v_pRaw_4737_ = l_Lean_Expr_appArg_x21(v_body_4686_);
                            crate::leanh::lean_dec_ref(v_body_4686_);
                            v___x_4738_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_4736_);
                            if crate::leanh::lean_obj_tag(v___x_4738_) == 1 {
                                crate::leanh::lean_dec_ref(v_pRaw_4736_);
                                v_val_4739_ = crate::leanh::lean_ctor_get(v___x_4738_, 0);
                                v_isSharedCheck_4809_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4738_)) as u8;
                                if v_isSharedCheck_4809_ == 0 {
                                    v___x_4741_ = v___x_4738_;
                                    v_isShared_4742_ = v_isSharedCheck_4809_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_4739_);
                                    crate::leanh::lean_dec(v___x_4738_);
                                    v___x_4741_ = crate::leanh::lean_box(0);
                                    v_isShared_4742_ = v_isSharedCheck_4809_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_4738_);
                                v___x_4810_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(v_pRaw_4737_);
                                crate::leanh::lean_dec_ref(v_pRaw_4737_);
                                if crate::leanh::lean_obj_tag(v___x_4810_) == 1 {
                                    v_val_4811_ = crate::leanh::lean_ctor_get(v___x_4810_, 0);
                                    v_isSharedCheck_4881_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4810_)) as u8;
                                    if v_isSharedCheck_4881_ == 0 {
                                        v___x_4813_ = v___x_4810_;
                                        v_isShared_4814_ = v_isSharedCheck_4881_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_4811_);
                                        crate::leanh::lean_dec(v___x_4810_);
                                        v___x_4813_ = crate::leanh::lean_box(0);
                                        v_isShared_4814_ = v_isSharedCheck_4881_;
                                        state = 19;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_4810_);
                                    crate::leanh::lean_dec_ref(v_pRaw_4736_);
                                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                                    crate::leanh::lean_dec(v_binderName_4684_);
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4698_);
                        crate::leanh::lean_dec_ref(v___x_4697_);
                        crate::leanh::lean_dec_ref(v_body_4686_);
                        crate::leanh::lean_dec_ref(v_binderType_4685_);
                        crate::leanh::lean_dec(v_binderName_4684_);
                        v___x_4882_ = l_Lean_Meta_Grind_simpForall___closed__0;
                        v___x_4883_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4883_, 0, v___x_4882_);
                        return v___x_4883_;
                    }
                }
            }
            3 => {
                v_expr_4715_ = l_Lean_mkAnd(v___x_4708_, v___x_4709_);
                v___x_4716_ = l_Lean_Meta_Grind_simpForall___closed__6;
                v___x_4717_ = crate::leanh::lean_box(0);
                v___x_4718_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4718_, 0, v_a_4711_);
                crate::leanh::lean_ctor_set(v___x_4718_, 1, v___x_4717_);
                v___x_4719_ = l_Lean_mkConst(v___x_4716_, v___x_4718_);
                v___x_4720_ = l_Lean_mkApp3(v___x_4719_, v_binderType_4685_, v_p_4706_, v_q_4707_);
                v___x_4721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4721_, 0, v___x_4720_);
                v___x_4722_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4722_, 0, v_expr_4715_);
                crate::leanh::lean_ctor_set(v___x_4722_, 1, v___x_4721_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4722_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_4696_,
                );
                v___x_4723_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4723_, 0, v___x_4722_);
                if v_isShared_4714_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4713_, 0, v___x_4723_);
                    v___x_4725_ = v___x_4713_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4726_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4723_);
                    v___x_4725_ = v_reuseFailAlloc_4726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4725_;
            }
            5 => {
                if v_isShared_4731_ == 0 {
                    v___x_4733_ = v___x_4730_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
                    v___x_4733_ = v_reuseFailAlloc_4734_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4733_;
            }
            7 => {
                v_snd_4743_ = crate::leanh::lean_ctor_get(v_val_4739_, 1);
                v_fst_4744_ = crate::leanh::lean_ctor_get(v_val_4739_, 0);
                v_isSharedCheck_4808_ = (!crate::leanh::lean_is_exclusive(v_val_4739_)) as u8;
                if v_isSharedCheck_4808_ == 0 {
                    v___x_4746_ = v_val_4739_;
                    v_isShared_4747_ = v_isSharedCheck_4808_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4743_);
                    crate::leanh::lean_inc(v_fst_4744_);
                    crate::leanh::lean_dec(v_val_4739_);
                    v___x_4746_ = crate::leanh::lean_box(0);
                    v_isShared_4747_ = v_isSharedCheck_4808_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_fst_4748_ = crate::leanh::lean_ctor_get(v_snd_4743_, 0);
                v_snd_4749_ = crate::leanh::lean_ctor_get(v_snd_4743_, 1);
                v_isSharedCheck_4807_ = (!crate::leanh::lean_is_exclusive(v_snd_4743_)) as u8;
                if v_isSharedCheck_4807_ == 0 {
                    v___x_4751_ = v_snd_4743_;
                    v_isShared_4752_ = v_isSharedCheck_4807_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4749_);
                    crate::leanh::lean_inc(v_fst_4748_);
                    crate::leanh::lean_dec(v_snd_4743_);
                    v___x_4751_ = crate::leanh::lean_box(0);
                    v_isShared_4752_ = v_isSharedCheck_4807_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc_ref(v_pRaw_4737_);
                crate::leanh::lean_inc_ref_n(v_binderType_4685_, 4);
                crate::leanh::lean_inc_n(v_binderName_4684_, 3);
                v_p_4753_ = l_Lean_mkLambda(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v_pRaw_4737_,
                );
                v___x_4754_ = 0;
                crate::leanh::lean_inc(v_snd_4749_);
                crate::leanh::lean_inc_n(v_fst_4748_, 2);
                crate::leanh::lean_inc(v_fst_4744_);
                v___x_4755_ = l_Lean_mkLambda(v_fst_4744_, v___x_4754_, v_fst_4748_, v_snd_4749_);
                v_q_4756_ = l_Lean_mkLambda(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v___x_4755_,
                );
                v_00_u03b2_4757_ = l_Lean_mkLambda(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v_fst_4748_,
                );
                v___x_4758_ = l_Lean_Meta_getLevel(
                    v_binderType_4685_,
                    v___y_4694_,
                    v___y_4691_,
                    v___y_4690_,
                    v___y_4695_,
                );
                if crate::leanh::lean_obj_tag(v___x_4758_) == 0 {
                    v_a_4759_ = crate::leanh::lean_ctor_get(v___x_4758_, 0);
                    crate::leanh::lean_inc(v_a_4759_);
                    crate::leanh::lean_dec_ref_known(v___x_4758_, 1);
                    crate::leanh::lean_inc(v_fst_4748_);
                    v___f_4760_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_simpForall___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4760_, 0, v_fst_4748_);
                    crate::leanh::lean_inc_ref(v_binderType_4685_);
                    crate::leanh::lean_inc(v_binderName_4684_);
                    v___x_4761_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_4684_, v_binderType_4685_, v___f_4760_, v___y_4689_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4691_, v___y_4690_, v___y_4695_);
                    if crate::leanh::lean_obj_tag(v___x_4761_) == 0 {
                        v_a_4762_ = crate::leanh::lean_ctor_get(v___x_4761_, 0);
                        v_isSharedCheck_4790_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4761_)) as u8;
                        if v_isSharedCheck_4790_ == 0 {
                            v___x_4764_ = v___x_4761_;
                            v_isShared_4765_ = v_isSharedCheck_4790_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4762_);
                            crate::leanh::lean_dec(v___x_4761_);
                            v___x_4764_ = crate::leanh::lean_box(0);
                            v_isShared_4765_ = v_isSharedCheck_4790_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4759_);
                        crate::leanh::lean_dec_ref(v_00_u03b2_4757_);
                        crate::leanh::lean_dec_ref(v_q_4756_);
                        crate::leanh::lean_dec_ref(v_p_4753_);
                        crate::leanh::lean_del_object(v___x_4751_);
                        crate::leanh::lean_dec(v_snd_4749_);
                        crate::leanh::lean_dec(v_fst_4748_);
                        crate::leanh::lean_del_object(v___x_4746_);
                        crate::leanh::lean_dec(v_fst_4744_);
                        crate::leanh::lean_del_object(v___x_4741_);
                        crate::leanh::lean_dec_ref(v_pRaw_4737_);
                        crate::leanh::lean_dec_ref(v_binderType_4685_);
                        crate::leanh::lean_dec(v_binderName_4684_);
                        v_a_4791_ = crate::leanh::lean_ctor_get(v___x_4761_, 0);
                        v_isSharedCheck_4798_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4761_)) as u8;
                        if v_isSharedCheck_4798_ == 0 {
                            v___x_4793_ = v___x_4761_;
                            v_isShared_4794_ = v_isSharedCheck_4798_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4791_);
                            crate::leanh::lean_dec(v___x_4761_);
                            v___x_4793_ = crate::leanh::lean_box(0);
                            v_isShared_4794_ = v_isSharedCheck_4798_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03b2_4757_);
                    crate::leanh::lean_dec_ref(v_q_4756_);
                    crate::leanh::lean_dec_ref(v_p_4753_);
                    crate::leanh::lean_del_object(v___x_4751_);
                    crate::leanh::lean_dec(v_snd_4749_);
                    crate::leanh::lean_dec(v_fst_4748_);
                    crate::leanh::lean_del_object(v___x_4746_);
                    crate::leanh::lean_dec(v_fst_4744_);
                    crate::leanh::lean_del_object(v___x_4741_);
                    crate::leanh::lean_dec_ref(v_pRaw_4737_);
                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v_a_4799_ = crate::leanh::lean_ctor_get(v___x_4758_, 0);
                    v_isSharedCheck_4806_ = (!crate::leanh::lean_is_exclusive(v___x_4758_)) as u8;
                    if v_isSharedCheck_4806_ == 0 {
                        v___x_4801_ = v___x_4758_;
                        v_isShared_4802_ = v_isSharedCheck_4806_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4799_);
                        crate::leanh::lean_dec(v___x_4758_);
                        v___x_4801_ = crate::leanh::lean_box(0);
                        v_isShared_4802_ = v_isSharedCheck_4806_;
                        state = 17;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4766_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4767_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4768_ = lean_expr_lift_loose_bvars(v_pRaw_4737_, v___x_4766_, v___x_4767_);
                crate::leanh::lean_dec_ref(v_pRaw_4737_);
                v___x_4769_ = l_Lean_mkOr(v_snd_4749_, v___x_4768_);
                v___x_4770_ = l_Lean_mkForall(v_fst_4744_, v___x_4754_, v_fst_4748_, v___x_4769_);
                crate::leanh::lean_inc_ref(v_binderType_4685_);
                v___x_4771_ = l_Lean_mkForall(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v___x_4770_,
                );
                v___x_4772_ = l_Lean_Meta_Grind_simpForall___closed__8;
                v___x_4773_ = crate::leanh::lean_box(0);
                if v_isShared_4752_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4751_, 1);
                    crate::leanh::lean_ctor_set(v___x_4751_, 1, v___x_4773_);
                    crate::leanh::lean_ctor_set(v___x_4751_, 0, v_a_4762_);
                    v___x_4775_ = v___x_4751_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4789_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4789_, 1, v___x_4773_);
                    v___x_4775_ = v_reuseFailAlloc_4789_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4747_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4746_, 1);
                    crate::leanh::lean_ctor_set(v___x_4746_, 1, v___x_4775_);
                    crate::leanh::lean_ctor_set(v___x_4746_, 0, v_a_4759_);
                    v___x_4777_ = v___x_4746_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4788_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4788_, 0, v_a_4759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4788_, 1, v___x_4775_);
                    v___x_4777_ = v_reuseFailAlloc_4788_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4778_ = l_Lean_mkConst(v___x_4772_, v___x_4777_);
                v___x_4779_ = l_Lean_mkApp4(
                    v___x_4778_,
                    v_binderType_4685_,
                    v_00_u03b2_4757_,
                    v_p_4753_,
                    v_q_4756_,
                );
                if v_isShared_4742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4741_, 0, v___x_4779_);
                    v___x_4781_ = v___x_4741_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4787_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4779_);
                    v___x_4781_ = v_reuseFailAlloc_4787_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_4782_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4782_, 0, v___x_4771_);
                crate::leanh::lean_ctor_set(v___x_4782_, 1, v___x_4781_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4782_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_4696_,
                );
                v___x_4783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4783_, 0, v___x_4782_);
                if v_isShared_4765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4764_, 0, v___x_4783_);
                    v___x_4785_ = v___x_4764_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4785_;
            }
            15 => {
                if v_isShared_4794_ == 0 {
                    v___x_4796_ = v___x_4793_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4797_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4797_, 0, v_a_4791_);
                    v___x_4796_ = v_reuseFailAlloc_4797_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4796_;
            }
            17 => {
                if v_isShared_4802_ == 0 {
                    v___x_4804_ = v___x_4801_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
                    v___x_4804_ = v_reuseFailAlloc_4805_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4804_;
            }
            19 => {
                v_snd_4815_ = crate::leanh::lean_ctor_get(v_val_4811_, 1);
                v_fst_4816_ = crate::leanh::lean_ctor_get(v_val_4811_, 0);
                v_isSharedCheck_4880_ = (!crate::leanh::lean_is_exclusive(v_val_4811_)) as u8;
                if v_isSharedCheck_4880_ == 0 {
                    v___x_4818_ = v_val_4811_;
                    v_isShared_4819_ = v_isSharedCheck_4880_;
                    state = 20;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4815_);
                    crate::leanh::lean_inc(v_fst_4816_);
                    crate::leanh::lean_dec(v_val_4811_);
                    v___x_4818_ = crate::leanh::lean_box(0);
                    v_isShared_4819_ = v_isSharedCheck_4880_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v_fst_4820_ = crate::leanh::lean_ctor_get(v_snd_4815_, 0);
                v_snd_4821_ = crate::leanh::lean_ctor_get(v_snd_4815_, 1);
                v_isSharedCheck_4879_ = (!crate::leanh::lean_is_exclusive(v_snd_4815_)) as u8;
                if v_isSharedCheck_4879_ == 0 {
                    v___x_4823_ = v_snd_4815_;
                    v_isShared_4824_ = v_isSharedCheck_4879_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4821_);
                    crate::leanh::lean_inc(v_fst_4820_);
                    crate::leanh::lean_dec(v_snd_4815_);
                    v___x_4823_ = crate::leanh::lean_box(0);
                    v_isShared_4824_ = v_isSharedCheck_4879_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                crate::leanh::lean_inc_ref(v_pRaw_4736_);
                crate::leanh::lean_inc_ref_n(v_binderType_4685_, 4);
                crate::leanh::lean_inc_n(v_binderName_4684_, 3);
                v_p_4825_ = l_Lean_mkLambda(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v_pRaw_4736_,
                );
                v___x_4826_ = 0;
                crate::leanh::lean_inc(v_snd_4821_);
                crate::leanh::lean_inc_n(v_fst_4820_, 2);
                crate::leanh::lean_inc(v_fst_4816_);
                v___x_4827_ = l_Lean_mkLambda(v_fst_4816_, v___x_4826_, v_fst_4820_, v_snd_4821_);
                v_q_4828_ = l_Lean_mkLambda(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v___x_4827_,
                );
                v_00_u03b2_4829_ = l_Lean_mkLambda(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v_fst_4820_,
                );
                v___x_4830_ = l_Lean_Meta_getLevel(
                    v_binderType_4685_,
                    v___y_4694_,
                    v___y_4691_,
                    v___y_4690_,
                    v___y_4695_,
                );
                if crate::leanh::lean_obj_tag(v___x_4830_) == 0 {
                    v_a_4831_ = crate::leanh::lean_ctor_get(v___x_4830_, 0);
                    crate::leanh::lean_inc(v_a_4831_);
                    crate::leanh::lean_dec_ref_known(v___x_4830_, 1);
                    crate::leanh::lean_inc(v_fst_4820_);
                    v___f_4832_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_simpForall___lam__0___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_4832_, 0, v_fst_4820_);
                    crate::leanh::lean_inc_ref(v_binderType_4685_);
                    crate::leanh::lean_inc(v_binderName_4684_);
                    v___x_4833_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(v_binderName_4684_, v_binderType_4685_, v___f_4832_, v___y_4689_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4691_, v___y_4690_, v___y_4695_);
                    if crate::leanh::lean_obj_tag(v___x_4833_) == 0 {
                        v_a_4834_ = crate::leanh::lean_ctor_get(v___x_4833_, 0);
                        v_isSharedCheck_4862_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4833_)) as u8;
                        if v_isSharedCheck_4862_ == 0 {
                            v___x_4836_ = v___x_4833_;
                            v_isShared_4837_ = v_isSharedCheck_4862_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4834_);
                            crate::leanh::lean_dec(v___x_4833_);
                            v___x_4836_ = crate::leanh::lean_box(0);
                            v_isShared_4837_ = v_isSharedCheck_4862_;
                            state = 22;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4831_);
                        crate::leanh::lean_dec_ref(v_00_u03b2_4829_);
                        crate::leanh::lean_dec_ref(v_q_4828_);
                        crate::leanh::lean_dec_ref(v_p_4825_);
                        crate::leanh::lean_del_object(v___x_4823_);
                        crate::leanh::lean_dec(v_snd_4821_);
                        crate::leanh::lean_dec(v_fst_4820_);
                        crate::leanh::lean_del_object(v___x_4818_);
                        crate::leanh::lean_dec(v_fst_4816_);
                        crate::leanh::lean_del_object(v___x_4813_);
                        crate::leanh::lean_dec_ref(v_pRaw_4736_);
                        crate::leanh::lean_dec_ref(v_binderType_4685_);
                        crate::leanh::lean_dec(v_binderName_4684_);
                        v_a_4863_ = crate::leanh::lean_ctor_get(v___x_4833_, 0);
                        v_isSharedCheck_4870_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4833_)) as u8;
                        if v_isSharedCheck_4870_ == 0 {
                            v___x_4865_ = v___x_4833_;
                            v_isShared_4866_ = v_isSharedCheck_4870_;
                            state = 27;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4863_);
                            crate::leanh::lean_dec(v___x_4833_);
                            v___x_4865_ = crate::leanh::lean_box(0);
                            v_isShared_4866_ = v_isSharedCheck_4870_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_00_u03b2_4829_);
                    crate::leanh::lean_dec_ref(v_q_4828_);
                    crate::leanh::lean_dec_ref(v_p_4825_);
                    crate::leanh::lean_del_object(v___x_4823_);
                    crate::leanh::lean_dec(v_snd_4821_);
                    crate::leanh::lean_dec(v_fst_4820_);
                    crate::leanh::lean_del_object(v___x_4818_);
                    crate::leanh::lean_dec(v_fst_4816_);
                    crate::leanh::lean_del_object(v___x_4813_);
                    crate::leanh::lean_dec_ref(v_pRaw_4736_);
                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v_a_4871_ = crate::leanh::lean_ctor_get(v___x_4830_, 0);
                    v_isSharedCheck_4878_ = (!crate::leanh::lean_is_exclusive(v___x_4830_)) as u8;
                    if v_isSharedCheck_4878_ == 0 {
                        v___x_4873_ = v___x_4830_;
                        v_isShared_4874_ = v_isSharedCheck_4878_;
                        state = 29;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4871_);
                        crate::leanh::lean_dec(v___x_4830_);
                        v___x_4873_ = crate::leanh::lean_box(0);
                        v_isShared_4874_ = v_isSharedCheck_4878_;
                        state = 29;
                        continue;
                    }
                }
            }
            22 => {
                v___x_4838_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4839_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4840_ = lean_expr_lift_loose_bvars(v_pRaw_4736_, v___x_4838_, v___x_4839_);
                crate::leanh::lean_dec_ref(v_pRaw_4736_);
                v___x_4841_ = l_Lean_mkOr(v___x_4840_, v_snd_4821_);
                v___x_4842_ = l_Lean_mkForall(v_fst_4816_, v___x_4826_, v_fst_4820_, v___x_4841_);
                crate::leanh::lean_inc_ref(v_binderType_4685_);
                v___x_4843_ = l_Lean_mkForall(
                    v_binderName_4684_,
                    v_binderInfo_4687_,
                    v_binderType_4685_,
                    v___x_4842_,
                );
                v___x_4844_ = l_Lean_Meta_Grind_simpForall___closed__10;
                v___x_4845_ = crate::leanh::lean_box(0);
                if v_isShared_4824_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4823_, 1);
                    crate::leanh::lean_ctor_set(v___x_4823_, 1, v___x_4845_);
                    crate::leanh::lean_ctor_set(v___x_4823_, 0, v_a_4834_);
                    v___x_4847_ = v___x_4823_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4834_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 1, v___x_4845_);
                    v___x_4847_ = v_reuseFailAlloc_4861_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_4819_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4818_, 1);
                    crate::leanh::lean_ctor_set(v___x_4818_, 1, v___x_4847_);
                    crate::leanh::lean_ctor_set(v___x_4818_, 0, v_a_4831_);
                    v___x_4849_ = v___x_4818_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4860_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 0, v_a_4831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4860_, 1, v___x_4847_);
                    v___x_4849_ = v_reuseFailAlloc_4860_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_4850_ = l_Lean_mkConst(v___x_4844_, v___x_4849_);
                v___x_4851_ = l_Lean_mkApp4(
                    v___x_4850_,
                    v_binderType_4685_,
                    v_00_u03b2_4829_,
                    v_p_4825_,
                    v_q_4828_,
                );
                if v_isShared_4814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4813_, 0, v___x_4851_);
                    v___x_4853_ = v___x_4813_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4859_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4851_);
                    v___x_4853_ = v_reuseFailAlloc_4859_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                v___x_4854_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4854_, 0, v___x_4843_);
                crate::leanh::lean_ctor_set(v___x_4854_, 1, v___x_4853_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4854_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___y_4696_,
                );
                v___x_4855_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4855_, 0, v___x_4854_);
                if v_isShared_4837_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4836_, 0, v___x_4855_);
                    v___x_4857_ = v___x_4836_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4855_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4857_;
            }
            27 => {
                if v_isShared_4866_ == 0 {
                    v___x_4868_ = v___x_4865_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4869_, 0, v_a_4863_);
                    v___x_4868_ = v_reuseFailAlloc_4869_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4868_;
            }
            29 => {
                if v_isShared_4874_ == 0 {
                    v___x_4876_ = v___x_4873_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
                    v___x_4876_ = v_reuseFailAlloc_4877_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4876_;
            }
            31 => {
                v___x_4892_ = l_Lean_Expr_isApp(v_body_4686_);
                if v___x_4892_ == 0 {
                    v___y_4689_ = v___y_4885_;
                    v___y_4690_ = v___y_4890_;
                    v___y_4691_ = v___y_4889_;
                    v___y_4692_ = v___y_4886_;
                    v___y_4693_ = v___y_4887_;
                    v___y_4694_ = v___y_4888_;
                    v___y_4695_ = v___y_4891_;
                    v___y_4696_ = v___x_4892_;
                    state = 2;
                    continue;
                } else {
                    v___x_4893_ = l_Lean_Expr_getAppNumArgs(v_body_4686_);
                    v___x_4894_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_4895_ = lean_nat_dec_eq(v___x_4893_, v___x_4894_);
                    crate::leanh::lean_dec(v___x_4893_);
                    v___y_4689_ = v___y_4885_;
                    v___y_4690_ = v___y_4890_;
                    v___y_4691_ = v___y_4889_;
                    v___y_4692_ = v___y_4886_;
                    v___y_4693_ = v___y_4887_;
                    v___y_4694_ = v___y_4888_;
                    v___y_4695_ = v___y_4891_;
                    v___y_4696_ = v___x_4895_;
                    state = 2;
                    continue;
                }
            }
            32 => {
                if crate::leanh::lean_obj_tag(v___y_4901_) == 0 {
                    v_a_4902_ = crate::leanh::lean_ctor_get(v___y_4901_, 0);
                    v_isSharedCheck_4916_ = (!crate::leanh::lean_is_exclusive(v___y_4901_)) as u8;
                    if v_isSharedCheck_4916_ == 0 {
                        v___x_4904_ = v___y_4901_;
                        v_isShared_4905_ = v_isSharedCheck_4916_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4902_);
                        crate::leanh::lean_dec(v___y_4901_);
                        v___x_4904_ = crate::leanh::lean_box(0);
                        v_isShared_4905_ = v_isSharedCheck_4916_;
                        state = 33;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_4686_);
                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v_a_4917_ = crate::leanh::lean_ctor_get(v___y_4901_, 0);
                    v_isSharedCheck_4924_ = (!crate::leanh::lean_is_exclusive(v___y_4901_)) as u8;
                    if v_isSharedCheck_4924_ == 0 {
                        v___x_4919_ = v___y_4901_;
                        v_isShared_4920_ = v_isSharedCheck_4924_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4917_);
                        crate::leanh::lean_dec(v___y_4901_);
                        v___x_4919_ = crate::leanh::lean_box(0);
                        v_isShared_4920_ = v_isSharedCheck_4924_;
                        state = 35;
                        continue;
                    }
                }
            }
            33 => {
                v___x_4906_ = (crate::leanh::lean_unbox(v_a_4902_) as u8);
                crate::leanh::lean_dec(v_a_4902_);
                if v___x_4906_ == 0 {
                    crate::leanh::lean_del_object(v___x_4904_);
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_4686_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v___x_4907_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__13,
                    );
                    v___x_4908_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__16),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__16_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__16,
                    );
                    v___x_4909_ = l_Lean_Expr_app___override(v___x_4908_, v_binderType_4685_);
                    v___x_4910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4910_, 0, v___x_4909_);
                    v___x_4911_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4911_, 0, v___x_4907_);
                    crate::leanh::lean_ctor_set(v___x_4911_, 1, v___x_4910_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4911_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_4899_,
                    );
                    v___x_4912_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4912_, 0, v___x_4911_);
                    if v_isShared_4905_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4904_, 0, v___x_4912_);
                        v___x_4914_ = v___x_4904_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_4915_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4912_);
                        v___x_4914_ = v_reuseFailAlloc_4915_;
                        state = 34;
                        continue;
                    }
                }
            }
            34 => {
                return v___x_4914_;
            }
            35 => {
                if v_isShared_4920_ == 0 {
                    v___x_4922_ = v___x_4919_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4923_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4917_);
                    v___x_4922_ = v_reuseFailAlloc_4923_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_4922_;
            }
            37 => {
                if v_a_4935_ == 0 {
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref_n(v_body_4932_, 2);
                    crate::leanh::lean_inc_ref_n(v_binderType_4931_, 3);
                    crate::leanh::lean_inc_n(v_binderName_4930_, 2);
                    crate::leanh::lean_dec_ref_known(v_binderType_4685_, 3);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v___x_4936_ = l_Lean_mkLambda(
                        v_binderName_4930_,
                        v_binderInfo_4933_,
                        v_binderType_4931_,
                        v_body_4932_,
                    );
                    v___x_4937_ = l_Lean_Meta_getLevel(
                        v_binderType_4931_,
                        v_a_4676_,
                        v_a_4677_,
                        v_a_4678_,
                        v_a_4679_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4937_) == 0 {
                        v_a_4938_ = crate::leanh::lean_ctor_get(v___x_4937_, 0);
                        v_isSharedCheck_4959_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4937_)) as u8;
                        if v_isSharedCheck_4959_ == 0 {
                            v___x_4940_ = v___x_4937_;
                            v_isShared_4941_ = v_isSharedCheck_4959_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4938_);
                            crate::leanh::lean_dec(v___x_4937_);
                            v___x_4940_ = crate::leanh::lean_box(0);
                            v_isShared_4941_ = v_isSharedCheck_4959_;
                            state = 38;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4936_);
                        crate::leanh::lean_dec_ref(v_body_4932_);
                        crate::leanh::lean_dec_ref(v_binderType_4931_);
                        crate::leanh::lean_dec(v_binderName_4930_);
                        crate::leanh::lean_dec_ref(v_body_4686_);
                        v_a_4960_ = crate::leanh::lean_ctor_get(v___x_4937_, 0);
                        v_isSharedCheck_4967_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4937_)) as u8;
                        if v_isSharedCheck_4967_ == 0 {
                            v___x_4962_ = v___x_4937_;
                            v_isShared_4963_ = v_isSharedCheck_4967_;
                            state = 40;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4960_);
                            crate::leanh::lean_dec(v___x_4937_);
                            v___x_4962_ = crate::leanh::lean_box(0);
                            v_isShared_4963_ = v_isSharedCheck_4967_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            38 => {
                v___x_4942_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
                v___x_4943_ = crate::leanh::lean_box(0);
                v___x_4944_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4944_, 0, v_a_4938_);
                crate::leanh::lean_ctor_set(v___x_4944_, 1, v___x_4943_);
                crate::leanh::lean_inc_ref(v___x_4944_);
                v___x_4945_ = l_Lean_mkConst(v___x_4942_, v___x_4944_);
                v___x_4946_ = l_Lean_mkNot(v_body_4932_);
                crate::leanh::lean_inc_ref_n(v_binderType_4931_, 2);
                v___x_4947_ = l_Lean_mkLambda(
                    v_binderName_4930_,
                    v_binderInfo_4933_,
                    v_binderType_4931_,
                    v___x_4946_,
                );
                v___x_4948_ = l_Lean_mkAppB(v___x_4945_, v_binderType_4931_, v___x_4947_);
                crate::leanh::lean_inc_ref(v_body_4686_);
                v___x_4949_ = l_Lean_mkOr(v___x_4948_, v_body_4686_);
                v___x_4950_ = l_Lean_Meta_Grind_simpForall___closed__18;
                v___x_4951_ = l_Lean_mkConst(v___x_4950_, v___x_4944_);
                v___x_4952_ =
                    l_Lean_mkApp3(v___x_4951_, v_binderType_4931_, v___x_4936_, v_body_4686_);
                v___x_4953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4953_, 0, v___x_4952_);
                v___x_4954_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4954_, 0, v___x_4949_);
                crate::leanh::lean_ctor_set(v___x_4954_, 1, v___x_4953_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4954_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_4899_,
                );
                v___x_4955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4955_, 0, v___x_4954_);
                if v_isShared_4941_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4940_, 0, v___x_4955_);
                    v___x_4957_ = v___x_4940_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4958_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4958_, 0, v___x_4955_);
                    v___x_4957_ = v_reuseFailAlloc_4958_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4957_;
            }
            40 => {
                if v_isShared_4963_ == 0 {
                    v___x_4965_ = v___x_4962_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_a_4960_);
                    v___x_4965_ = v_reuseFailAlloc_4966_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4965_;
            }
            42 => {
                if v_isShared_4975_ == 0 {
                    v___x_4977_ = v___x_4974_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4978_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4978_, 0, v_a_4972_);
                    v___x_4977_ = v_reuseFailAlloc_4978_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4977_;
            }
            44 => {
                v___x_4994_ = (crate::leanh::lean_unbox(v_a_4990_) as u8);
                crate::leanh::lean_dec(v_a_4990_);
                if v___x_4994_ == 0 {
                    crate::leanh::lean_del_object(v___x_4992_);
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_4686_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v___x_4995_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__13,
                    );
                    v___x_4996_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__21),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__21_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__21,
                    );
                    v___x_4997_ = l_Lean_Expr_app___override(v___x_4996_, v_binderType_4685_);
                    v___x_4998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4998_, 0, v___x_4997_);
                    v___x_4999_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4999_, 0, v___x_4995_);
                    crate::leanh::lean_ctor_set(v___x_4999_, 1, v___x_4998_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4999_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_4899_,
                    );
                    v___x_5000_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5000_, 0, v___x_4999_);
                    if v_isShared_4993_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4992_, 0, v___x_5000_);
                        v___x_5002_ = v___x_4992_;
                        state = 45;
                        continue;
                    } else {
                        v_reuseFailAlloc_5003_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5003_, 0, v___x_5000_);
                        v___x_5002_ = v_reuseFailAlloc_5003_;
                        state = 45;
                        continue;
                    }
                }
            }
            45 => {
                return v___x_5002_;
            }
            46 => {
                if v_isShared_5008_ == 0 {
                    v___x_5010_ = v___x_5007_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5011_, 0, v_a_5005_);
                    v___x_5010_ = v_reuseFailAlloc_5011_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_5010_;
            }
            48 => {
                v___x_5018_ = (crate::leanh::lean_unbox(v_a_5014_) as u8);
                crate::leanh::lean_dec(v_a_5014_);
                if v___x_5018_ == 0 {
                    crate::leanh::lean_del_object(v___x_5016_);
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_4686_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    crate::leanh::lean_inc_ref(v_binderType_4685_);
                    v___x_5019_ = l_Lean_mkNot(v_binderType_4685_);
                    v___x_5020_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__24),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__24_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__24,
                    );
                    v___x_5021_ = l_Lean_Expr_app___override(v___x_5020_, v_binderType_4685_);
                    v___x_5022_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5022_, 0, v___x_5021_);
                    v___x_5023_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5023_, 0, v___x_5019_);
                    crate::leanh::lean_ctor_set(v___x_5023_, 1, v___x_5022_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5023_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_4899_,
                    );
                    v___x_5024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5024_, 0, v___x_5023_);
                    if v_isShared_5017_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5016_, 0, v___x_5024_);
                        v___x_5026_ = v___x_5016_;
                        state = 49;
                        continue;
                    } else {
                        v_reuseFailAlloc_5027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5024_);
                        v___x_5026_ = v_reuseFailAlloc_5027_;
                        state = 49;
                        continue;
                    }
                }
            }
            49 => {
                return v___x_5026_;
            }
            50 => {
                if v_isShared_5032_ == 0 {
                    v___x_5034_ = v___x_5031_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_5034_;
            }
            52 => {
                if v_isShared_5040_ == 0 {
                    v___x_5042_ = v___x_5039_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
                    v___x_5042_ = v_reuseFailAlloc_5043_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_5042_;
            }
            54 => {
                v___x_5050_ = (crate::leanh::lean_unbox(v_a_5046_) as u8);
                crate::leanh::lean_dec(v_a_5046_);
                if v___x_5050_ == 0 {
                    crate::leanh::lean_del_object(v___x_5048_);
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v___x_5051_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__27),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__27_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__27,
                    );
                    crate::leanh::lean_inc_ref(v_body_4686_);
                    v___x_5052_ = l_Lean_Expr_app___override(v___x_5051_, v_body_4686_);
                    v___x_5053_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5053_, 0, v___x_5052_);
                    v___x_5054_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5054_, 0, v_body_4686_);
                    crate::leanh::lean_ctor_set(v___x_5054_, 1, v___x_5053_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5054_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_4899_,
                    );
                    v___x_5055_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5055_, 0, v___x_5054_);
                    if v_isShared_5049_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5048_, 0, v___x_5055_);
                        v___x_5057_ = v___x_5048_;
                        state = 55;
                        continue;
                    } else {
                        v_reuseFailAlloc_5058_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5058_, 0, v___x_5055_);
                        v___x_5057_ = v_reuseFailAlloc_5058_;
                        state = 55;
                        continue;
                    }
                }
            }
            55 => {
                return v___x_5057_;
            }
            56 => {
                if v_isShared_5063_ == 0 {
                    v___x_5065_ = v___x_5062_;
                    state = 57;
                    continue;
                } else {
                    v_reuseFailAlloc_5066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
                    v___x_5065_ = v_reuseFailAlloc_5066_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                return v___x_5065_;
            }
            58 => {
                v___x_5073_ = (crate::leanh::lean_unbox(v_a_5069_) as u8);
                crate::leanh::lean_dec(v_a_5069_);
                if v___x_5073_ == 0 {
                    crate::leanh::lean_del_object(v___x_5071_);
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v___x_5074_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__13,
                    );
                    v___x_5075_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__30),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__30_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__30,
                    );
                    v___x_5076_ = l_Lean_Expr_app___override(v___x_5075_, v_body_4686_);
                    v___x_5077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5077_, 0, v___x_5076_);
                    v___x_5078_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5078_, 0, v___x_5074_);
                    crate::leanh::lean_ctor_set(v___x_5078_, 1, v___x_5077_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5078_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_4899_,
                    );
                    v___x_5079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5079_, 0, v___x_5078_);
                    if v_isShared_5072_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5071_, 0, v___x_5079_);
                        v___x_5081_ = v___x_5071_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_5082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5079_);
                        v___x_5081_ = v_reuseFailAlloc_5082_;
                        state = 59;
                        continue;
                    }
                }
            }
            59 => {
                return v___x_5081_;
            }
            60 => {
                if v_isShared_5087_ == 0 {
                    v___x_5089_ = v___x_5086_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_5090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5090_, 0, v_a_5084_);
                    v___x_5089_ = v_reuseFailAlloc_5090_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_5089_;
            }
            62 => {
                if v_isShared_5095_ == 0 {
                    v___x_5097_ = v___x_5094_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_5098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_a_5092_);
                    v___x_5097_ = v_reuseFailAlloc_5098_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_5097_;
            }
            64 => {
                v___x_5114_ = (crate::leanh::lean_unbox(v_a_5110_) as u8);
                crate::leanh::lean_dec(v_a_5110_);
                if v___x_5114_ == 0 {
                    crate::leanh::lean_del_object(v___x_5112_);
                    crate::leanh::lean_dec_ref(v___x_5108_);
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    v___x_5115_ = l_Lean_mkLambda(
                        v_binderName_4684_,
                        v_binderInfo_4687_,
                        v_binderType_4685_,
                        v_body_4686_,
                    );
                    v___x_5116_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__36),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__36_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__36,
                    );
                    v___x_5117_ = l_Lean_Expr_app___override(v___x_5116_, v___x_5115_);
                    v___x_5118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5118_, 0, v___x_5117_);
                    v___x_5119_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5119_, 0, v___x_5108_);
                    crate::leanh::lean_ctor_set(v___x_5119_, 1, v___x_5118_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5119_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_4896_,
                    );
                    v___x_5120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5120_, 0, v___x_5119_);
                    if v_isShared_5113_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5112_, 0, v___x_5120_);
                        v___x_5122_ = v___x_5112_;
                        state = 65;
                        continue;
                    } else {
                        v_reuseFailAlloc_5123_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5123_, 0, v___x_5120_);
                        v___x_5122_ = v_reuseFailAlloc_5123_;
                        state = 65;
                        continue;
                    }
                }
            }
            65 => {
                return v___x_5122_;
            }
            66 => {
                if v_isShared_5128_ == 0 {
                    v___x_5130_ = v___x_5127_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_5131_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
                    v___x_5130_ = v_reuseFailAlloc_5131_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_5130_;
            }
            68 => {
                v___x_5143_ = (crate::leanh::lean_unbox(v_a_5139_) as u8);
                crate::leanh::lean_dec(v_a_5139_);
                if v___x_5143_ == 0 {
                    crate::leanh::lean_del_object(v___x_5141_);
                    crate::leanh::lean_dec_ref(v___x_5133_);
                    v___y_4885_ = v_a_4673_;
                    v___y_4886_ = v_a_4674_;
                    v___y_4887_ = v_a_4675_;
                    v___y_4888_ = v_a_4676_;
                    v___y_4889_ = v_a_4677_;
                    v___y_4890_ = v_a_4678_;
                    v___y_4891_ = v_a_4679_;
                    state = 31;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_body_4686_);
                    crate::leanh::lean_dec_ref(v_binderType_4685_);
                    crate::leanh::lean_dec(v_binderName_4684_);
                    v___x_5144_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__13_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__13,
                    );
                    v___x_5145_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__41),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpForall___closed__41_once),
                        _init_l_Lean_Meta_Grind_simpForall___closed__41,
                    );
                    v___x_5146_ = l_Lean_Expr_app___override(v___x_5145_, v___x_5133_);
                    v___x_5147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5147_, 0, v___x_5146_);
                    v___x_5148_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5148_, 0, v___x_5144_);
                    crate::leanh::lean_ctor_set(v___x_5148_, 1, v___x_5147_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5148_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_4896_,
                    );
                    v___x_5149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5149_, 0, v___x_5148_);
                    if v_isShared_5142_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5141_, 0, v___x_5149_);
                        v___x_5151_ = v___x_5141_;
                        state = 69;
                        continue;
                    } else {
                        v_reuseFailAlloc_5152_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5152_, 0, v___x_5149_);
                        v___x_5151_ = v_reuseFailAlloc_5152_;
                        state = 69;
                        continue;
                    }
                }
            }
            69 => {
                return v___x_5151_;
            }
            70 => {
                if v_isShared_5157_ == 0 {
                    v___x_5159_ = v___x_5156_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_5160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5160_, 0, v_a_5154_);
                    v___x_5159_ = v_reuseFailAlloc_5160_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                return v___x_5159_;
            }
            72 => {
                if v_isShared_5165_ == 0 {
                    v___x_5167_ = v___x_5164_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_5168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5168_, 0, v_a_5162_);
                    v___x_5167_ = v_reuseFailAlloc_5168_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_5167_;
            }
            74 => {
                if v_isShared_5173_ == 0 {
                    v___x_5175_ = v___x_5172_;
                    state = 75;
                    continue;
                } else {
                    v_reuseFailAlloc_5176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5170_);
                    v___x_5175_ = v_reuseFailAlloc_5176_;
                    state = 75;
                    continue;
                }
            }
            75 => {
                return v___x_5175_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpForall___boxed(
    mut v_e_5180_: *mut crate::leanh::LeanObject,
    mut v_a_5181_: *mut crate::leanh::LeanObject,
    mut v_a_5182_: *mut crate::leanh::LeanObject,
    mut v_a_5183_: *mut crate::leanh::LeanObject,
    mut v_a_5184_: *mut crate::leanh::LeanObject,
    mut v_a_5185_: *mut crate::leanh::LeanObject,
    mut v_a_5186_: *mut crate::leanh::LeanObject,
    mut v_a_5187_: *mut crate::leanh::LeanObject,
    mut v_a_5188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5189_ = l_Lean_Meta_Grind_simpForall(
        v_e_5180_, v_a_5181_, v_a_5182_, v_a_5183_, v_a_5184_, v_a_5185_, v_a_5186_, v_a_5187_,
    );
    crate::leanh::lean_dec(v_a_5187_);
    crate::leanh::lean_dec_ref(v_a_5186_);
    crate::leanh::lean_dec(v_a_5185_);
    crate::leanh::lean_dec_ref(v_a_5184_);
    crate::leanh::lean_dec(v_a_5183_);
    crate::leanh::lean_dec_ref(v_a_5182_);
    crate::leanh::lean_dec(v_a_5181_);
    return v_res_5189_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(
    mut v_00_u03b1_5190_: *mut crate::leanh::LeanObject,
    mut v_name_5191_: *mut crate::leanh::LeanObject,
    mut v_bi_5192_: u8,
    mut v_type_5193_: *mut crate::leanh::LeanObject,
    mut v_k_5194_: *mut crate::leanh::LeanObject,
    mut v_kind_5195_: u8,
    mut v___y_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
    mut v___y_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5204_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(v_name_5191_, v_bi_5192_, v_type_5193_, v_k_5194_, v_kind_5195_, v___y_5196_, v___y_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_);
    return v___x_5204_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(
    mut v_00_u03b1_5205_: *mut crate::leanh::LeanObject,
    mut v_name_5206_: *mut crate::leanh::LeanObject,
    mut v_bi_5207_: *mut crate::leanh::LeanObject,
    mut v_type_5208_: *mut crate::leanh::LeanObject,
    mut v_k_5209_: *mut crate::leanh::LeanObject,
    mut v_kind_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
    mut v___y_5216_: *mut crate::leanh::LeanObject,
    mut v___y_5217_: *mut crate::leanh::LeanObject,
    mut v___y_5218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_5219_: u8 = 0;
    let mut v_kind_boxed_5220_: u8 = 0;
    let mut v_res_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_5219_ = (crate::leanh::lean_unbox(v_bi_5207_) as u8);
    v_kind_boxed_5220_ = (crate::leanh::lean_unbox(v_kind_5210_) as u8);
    v_res_5221_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(v_00_u03b1_5205_, v_name_5206_, v_bi_boxed_5219_, v_type_5208_, v_k_5209_, v_kind_boxed_5220_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_, v___y_5215_, v___y_5216_, v___y_5217_);
    crate::leanh::lean_dec(v___y_5217_);
    crate::leanh::lean_dec_ref(v___y_5216_);
    crate::leanh::lean_dec(v___y_5215_);
    crate::leanh::lean_dec_ref(v___y_5214_);
    crate::leanh::lean_dec(v___y_5213_);
    crate::leanh::lean_dec_ref(v___y_5212_);
    crate::leanh::lean_dec(v___y_5211_);
    return v_res_5221_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(
    mut v_00_u03b1_5222_: *mut crate::leanh::LeanObject,
    mut v_name_5223_: *mut crate::leanh::LeanObject,
    mut v_type_5224_: *mut crate::leanh::LeanObject,
    mut v_k_5225_: *mut crate::leanh::LeanObject,
    mut v___y_5226_: *mut crate::leanh::LeanObject,
    mut v___y_5227_: *mut crate::leanh::LeanObject,
    mut v___y_5228_: *mut crate::leanh::LeanObject,
    mut v___y_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
    mut v___y_5231_: *mut crate::leanh::LeanObject,
    mut v___y_5232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5234_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(
        v_name_5223_,
        v_type_5224_,
        v_k_5225_,
        v___y_5226_,
        v___y_5227_,
        v___y_5228_,
        v___y_5229_,
        v___y_5230_,
        v___y_5231_,
        v___y_5232_,
    );
    return v___x_5234_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(
    mut v_00_u03b1_5235_: *mut crate::leanh::LeanObject,
    mut v_name_5236_: *mut crate::leanh::LeanObject,
    mut v_type_5237_: *mut crate::leanh::LeanObject,
    mut v_k_5238_: *mut crate::leanh::LeanObject,
    mut v___y_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
    mut v___y_5243_: *mut crate::leanh::LeanObject,
    mut v___y_5244_: *mut crate::leanh::LeanObject,
    mut v___y_5245_: *mut crate::leanh::LeanObject,
    mut v___y_5246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5247_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(
        v_00_u03b1_5235_,
        v_name_5236_,
        v_type_5237_,
        v_k_5238_,
        v___y_5239_,
        v___y_5240_,
        v___y_5241_,
        v___y_5242_,
        v___y_5243_,
        v___y_5244_,
        v___y_5245_,
    );
    crate::leanh::lean_dec(v___y_5245_);
    crate::leanh::lean_dec_ref(v___y_5244_);
    crate::leanh::lean_dec(v___y_5243_);
    crate::leanh::lean_dec_ref(v___y_5242_);
    crate::leanh::lean_dec(v___y_5241_);
    crate::leanh::lean_dec_ref(v___y_5240_);
    crate::leanh::lean_dec(v___y_5239_);
    return v_res_5247_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5262_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
    v___x_5263_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
    v___x_5264_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpForall___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5265_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5262_, v___x_5263_, v___x_5264_);
    return v___x_5265_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11____boxed(
    mut v_a_5266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5267_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
    return v_res_5267_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5281_ = crate::leanh::lean_box(0);
    v___x_5282_ = l_Lean_Meta_Grind_simpExists___redArg___closed__5;
    v___x_5283_ = l_Lean_mkConst(v___x_5282_, v___x_5281_);
    return v___x_5283_;
}
pub unsafe fn l_Lean_Meta_Grind_simpExists___redArg(
    mut v_e_5299_: *mut crate::leanh::LeanObject,
    mut v_a_5300_: *mut crate::leanh::LeanObject,
    mut v_a_5301_: *mut crate::leanh::LeanObject,
    mut v_a_5302_: *mut crate::leanh::LeanObject,
    mut v_a_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: u8 = 0;
    let mut v_arg_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: u8 = 0;
    let mut v_arg_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: u8 = 0;
    let mut v_binderName_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: u8 = 0;
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5332_: u8 = 0;
    let mut v___x_5333_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v_val_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5358_: u8 = 0;
    let mut v_isSharedCheck_5359_: u8 = 0;
    let mut v_a_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5363_: u8 = 0;
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5367_: u8 = 0;
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5377_: u8 = 0;
    let mut v_a_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5381_: u8 = 0;
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut v___y_5387_: u8 = 0;
    let mut v___y_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5390_: u8 = 0;
    let mut v___x_5391_: u8 = 0;
    let mut v___x_5392_: u8 = 0;
    let mut v_p_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: u8 = 0;
    let mut v_p_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5417_: u8 = 0;
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: u8 = 0;
    let mut v_b_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: u8 = 0;
    let mut v_pRaw_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_qRaw_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: u8 = 0;
    let mut v_p_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: u8 = 0;
    let mut v___x_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: u8 = 0;
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5311_ = l_Lean_Expr_cleanupAnnotations(v_e_5299_);
                v___x_5312_ = l_Lean_Expr_isApp(v___x_5311_);
                if v___x_5312_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5311_);
                    state = 1;
                    continue;
                } else {
                    v_arg_5313_ = crate::leanh::lean_ctor_get(v___x_5311_, 1);
                    crate::leanh::lean_inc_ref(v_arg_5313_);
                    v___x_5314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5311_);
                    v___x_5315_ = l_Lean_Expr_isApp(v___x_5314_);
                    if v___x_5315_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5314_);
                        crate::leanh::lean_dec_ref(v_arg_5313_);
                        state = 1;
                        continue;
                    } else {
                        v_arg_5316_ = crate::leanh::lean_ctor_get(v___x_5314_, 1);
                        crate::leanh::lean_inc_ref(v_arg_5316_);
                        v___x_5317_ = l_Lean_Expr_appFnCleanup___redArg(v___x_5314_);
                        v___x_5318_ = l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
                        v___x_5319_ = l_Lean_Expr_isConstOf(v___x_5317_, v___x_5318_);
                        if v___x_5319_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_5317_);
                            crate::leanh::lean_dec_ref(v_arg_5316_);
                            crate::leanh::lean_dec_ref(v_arg_5313_);
                            state = 1;
                            continue;
                        } else {
                            if crate::leanh::lean_obj_tag(v_arg_5313_) == 6 {
                                v_binderName_5320_ = crate::leanh::lean_ctor_get(v_arg_5313_, 0);
                                crate::leanh::lean_inc(v_binderName_5320_);
                                v_body_5321_ = crate::leanh::lean_ctor_get(v_arg_5313_, 2);
                                crate::leanh::lean_inc_ref(v_body_5321_);
                                crate::leanh::lean_dec_ref_known(v_arg_5313_, 3);
                                v___x_5446_ = l_Lean_Expr_isApp(v_body_5321_);
                                if v___x_5446_ == 0 {
                                    v___y_5417_ = v___x_5446_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___x_5447_ = l_Lean_Expr_getAppNumArgs(v_body_5321_);
                                    v___x_5448_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_5449_ = lean_nat_dec_eq(v___x_5447_, v___x_5448_);
                                    crate::leanh::lean_dec(v___x_5447_);
                                    v___y_5417_ = v___x_5449_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5317_);
                                crate::leanh::lean_dec_ref(v_arg_5316_);
                                crate::leanh::lean_dec_ref(v_arg_5313_);
                                v___x_5450_ = l_Lean_Meta_Grind_simpForall___closed__0;
                                v___x_5451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5451_, 0, v___x_5450_);
                                return v___x_5451_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5306_ = l_Lean_Meta_Grind_simpForall___closed__0;
                v___x_5307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5307_, 0, v___x_5306_);
                return v___x_5307_;
            }
            2 => {
                v___x_5309_ = l_Lean_Meta_Grind_simpForall___closed__0;
                v___x_5310_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5310_, 0, v___x_5309_);
                return v___x_5310_;
            }
            3 => {
                v___x_5327_ = l_Lean_Expr_hasLooseBVars(v_body_5321_);
                if v___x_5327_ == 0 {
                    if v___x_5319_ == 0 {
                        crate::leanh::lean_dec_ref(v_body_5321_);
                        crate::leanh::lean_dec_ref(v___x_5317_);
                        crate::leanh::lean_dec_ref(v_arg_5316_);
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_arg_5316_);
                        v___x_5328_ = l_Lean_Meta_isProp(
                            v_arg_5316_,
                            v___y_5323_,
                            v___y_5324_,
                            v___y_5325_,
                            v___y_5326_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5328_) == 0 {
                            v_a_5329_ = crate::leanh::lean_ctor_get(v___x_5328_, 0);
                            v_isSharedCheck_5377_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5328_)) as u8;
                            if v_isSharedCheck_5377_ == 0 {
                                v___x_5331_ = v___x_5328_;
                                v_isShared_5332_ = v_isSharedCheck_5377_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5329_);
                                crate::leanh::lean_dec(v___x_5328_);
                                v___x_5331_ = crate::leanh::lean_box(0);
                                v_isShared_5332_ = v_isSharedCheck_5377_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_5321_);
                            crate::leanh::lean_dec_ref(v___x_5317_);
                            crate::leanh::lean_dec_ref(v_arg_5316_);
                            v_a_5378_ = crate::leanh::lean_ctor_get(v___x_5328_, 0);
                            v_isSharedCheck_5385_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5328_)) as u8;
                            if v_isSharedCheck_5385_ == 0 {
                                v___x_5380_ = v___x_5328_;
                                v_isShared_5381_ = v_isSharedCheck_5385_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5378_);
                                crate::leanh::lean_dec(v___x_5328_);
                                v___x_5380_ = crate::leanh::lean_box(0);
                                v_isShared_5381_ = v_isSharedCheck_5385_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_5321_);
                    crate::leanh::lean_dec_ref(v___x_5317_);
                    crate::leanh::lean_dec_ref(v_arg_5316_);
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_5333_ = (crate::leanh::lean_unbox(v_a_5329_) as u8);
                crate::leanh::lean_dec(v_a_5329_);
                if v___x_5333_ == 0 {
                    crate::leanh::lean_del_object(v___x_5331_);
                    v___x_5334_ = l_Lean_Expr_constLevels_x21(v___x_5317_);
                    crate::leanh::lean_dec_ref(v___x_5317_);
                    v___x_5335_ = l_Lean_Meta_Grind_simpExists___redArg___closed__1;
                    crate::leanh::lean_inc(v___x_5334_);
                    v___x_5336_ = l_Lean_mkConst(v___x_5335_, v___x_5334_);
                    crate::leanh::lean_inc_ref(v_arg_5316_);
                    v___x_5337_ = l_Lean_Expr_app___override(v___x_5336_, v_arg_5316_);
                    v___x_5338_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_5337_,
                        v___y_5323_,
                        v___y_5324_,
                        v___y_5325_,
                        v___y_5326_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5338_) == 0 {
                        v_a_5339_ = crate::leanh::lean_ctor_get(v___x_5338_, 0);
                        v_isSharedCheck_5359_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5338_)) as u8;
                        if v_isSharedCheck_5359_ == 0 {
                            v___x_5341_ = v___x_5338_;
                            v_isShared_5342_ = v_isSharedCheck_5359_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5339_);
                            crate::leanh::lean_dec(v___x_5338_);
                            v___x_5341_ = crate::leanh::lean_box(0);
                            v_isShared_5342_ = v_isSharedCheck_5359_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5334_);
                        crate::leanh::lean_dec_ref(v_body_5321_);
                        crate::leanh::lean_dec_ref(v_arg_5316_);
                        v_a_5360_ = crate::leanh::lean_ctor_get(v___x_5338_, 0);
                        v_isSharedCheck_5367_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5338_)) as u8;
                        if v_isSharedCheck_5367_ == 0 {
                            v___x_5362_ = v___x_5338_;
                            v_isShared_5363_ = v_isSharedCheck_5367_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5360_);
                            crate::leanh::lean_dec(v___x_5338_);
                            v___x_5362_ = crate::leanh::lean_box(0);
                            v_isShared_5363_ = v_isSharedCheck_5367_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5317_);
                    crate::leanh::lean_inc_ref(v_body_5321_);
                    crate::leanh::lean_inc_ref(v_arg_5316_);
                    v___x_5368_ = l_Lean_mkAnd(v_arg_5316_, v_body_5321_);
                    v___x_5369_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpExists___redArg___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpExists___redArg___closed__6_once
                        ),
                        _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6,
                    );
                    v___x_5370_ = l_Lean_mkAppB(v___x_5369_, v_arg_5316_, v_body_5321_);
                    v___x_5371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5371_, 0, v___x_5370_);
                    v___x_5372_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5372_, 0, v___x_5368_);
                    crate::leanh::lean_ctor_set(v___x_5372_, 1, v___x_5371_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5372_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_5319_,
                    );
                    v___x_5373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5373_, 0, v___x_5372_);
                    if v_isShared_5332_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5331_, 0, v___x_5373_);
                        v___x_5375_ = v___x_5331_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_5376_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5376_, 0, v___x_5373_);
                        v___x_5375_ = v_reuseFailAlloc_5376_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_5339_) == 1 {
                    v_val_5343_ = crate::leanh::lean_ctor_get(v_a_5339_, 0);
                    v_isSharedCheck_5358_ = (!crate::leanh::lean_is_exclusive(v_a_5339_)) as u8;
                    if v_isSharedCheck_5358_ == 0 {
                        v___x_5345_ = v_a_5339_;
                        v_isShared_5346_ = v_isSharedCheck_5358_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5343_);
                        crate::leanh::lean_dec(v_a_5339_);
                        v___x_5345_ = crate::leanh::lean_box(0);
                        v_isShared_5346_ = v_isSharedCheck_5358_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5341_);
                    crate::leanh::lean_dec(v_a_5339_);
                    crate::leanh::lean_dec(v___x_5334_);
                    crate::leanh::lean_dec_ref(v_body_5321_);
                    crate::leanh::lean_dec_ref(v_arg_5316_);
                    state = 2;
                    continue;
                }
            }
            6 => {
                v___x_5347_ = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
                v___x_5348_ = l_Lean_mkConst(v___x_5347_, v___x_5334_);
                crate::leanh::lean_inc_ref(v_body_5321_);
                v___x_5349_ = l_Lean_mkApp3(v___x_5348_, v_arg_5316_, v_val_5343_, v_body_5321_);
                if v_isShared_5346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5345_, 0, v___x_5349_);
                    v___x_5351_ = v___x_5345_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5357_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5349_);
                    v___x_5351_ = v_reuseFailAlloc_5357_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_5352_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_5352_, 0, v_body_5321_);
                crate::leanh::lean_ctor_set(v___x_5352_, 1, v___x_5351_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5352_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_5319_,
                );
                v___x_5353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5353_, 0, v___x_5352_);
                if v_isShared_5342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5341_, 0, v___x_5353_);
                    v___x_5355_ = v___x_5341_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5353_);
                    v___x_5355_ = v_reuseFailAlloc_5356_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5355_;
            }
            9 => {
                if v_isShared_5363_ == 0 {
                    v___x_5365_ = v___x_5362_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5366_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
                    v___x_5365_ = v_reuseFailAlloc_5366_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5365_;
            }
            11 => {
                return v___x_5375_;
            }
            12 => {
                if v_isShared_5381_ == 0 {
                    v___x_5383_ = v___x_5380_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
                    v___x_5383_ = v_reuseFailAlloc_5384_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5383_;
            }
            14 => {
                if v___y_5390_ == 0 {
                    v___x_5391_ = l_Lean_Expr_hasLooseBVars(v___y_5389_);
                    if v___x_5391_ == 0 {
                        if v___y_5387_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_5389_);
                            crate::leanh::lean_dec_ref(v___y_5388_);
                            crate::leanh::lean_dec(v_binderName_5320_);
                            v___y_5323_ = v_a_5300_;
                            v___y_5324_ = v_a_5301_;
                            v___y_5325_ = v_a_5302_;
                            v___y_5326_ = v_a_5303_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_body_5321_);
                            v___x_5392_ = 0;
                            crate::leanh::lean_inc_ref_n(v_arg_5316_, 2);
                            v_p_5393_ = l_Lean_mkLambda(
                                v_binderName_5320_,
                                v___x_5392_,
                                v_arg_5316_,
                                v___y_5388_,
                            );
                            crate::leanh::lean_inc_ref(v_p_5393_);
                            crate::leanh::lean_inc_ref(v___x_5317_);
                            v___x_5394_ = l_Lean_mkAppB(v___x_5317_, v_arg_5316_, v_p_5393_);
                            crate::leanh::lean_inc_ref(v___y_5389_);
                            v_expr_5395_ = l_Lean_mkAnd(v___x_5394_, v___y_5389_);
                            v_u_5396_ = l_Lean_Expr_constLevels_x21(v___x_5317_);
                            crate::leanh::lean_dec_ref(v___x_5317_);
                            v___x_5397_ = l_Lean_Meta_Grind_simpExists___redArg___closed__8;
                            v___x_5398_ = l_Lean_mkConst(v___x_5397_, v_u_5396_);
                            v___x_5399_ =
                                l_Lean_mkApp3(v___x_5398_, v_arg_5316_, v_p_5393_, v___y_5389_);
                            v___x_5400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5400_, 0, v___x_5399_);
                            v___x_5401_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_5401_, 0, v_expr_5395_);
                            crate::leanh::lean_ctor_set(v___x_5401_, 1, v___x_5400_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_5401_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_5319_,
                            );
                            v___x_5402_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5402_, 0, v___x_5401_);
                            v___x_5403_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5403_, 0, v___x_5402_);
                            return v___x_5403_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_5389_);
                        crate::leanh::lean_dec_ref(v___y_5388_);
                        crate::leanh::lean_dec(v_binderName_5320_);
                        v___y_5323_ = v_a_5300_;
                        v___y_5324_ = v_a_5301_;
                        v___y_5325_ = v_a_5302_;
                        v___y_5326_ = v_a_5303_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_body_5321_);
                    v___x_5404_ = 0;
                    crate::leanh::lean_inc_ref_n(v_arg_5316_, 2);
                    v_p_5405_ =
                        l_Lean_mkLambda(v_binderName_5320_, v___x_5404_, v_arg_5316_, v___y_5389_);
                    crate::leanh::lean_inc_ref(v_p_5405_);
                    crate::leanh::lean_inc_ref(v___x_5317_);
                    v___x_5406_ = l_Lean_mkAppB(v___x_5317_, v_arg_5316_, v_p_5405_);
                    crate::leanh::lean_inc_ref(v___y_5388_);
                    v_expr_5407_ = l_Lean_mkAnd(v___y_5388_, v___x_5406_);
                    v_u_5408_ = l_Lean_Expr_constLevels_x21(v___x_5317_);
                    crate::leanh::lean_dec_ref(v___x_5317_);
                    v___x_5409_ = l_Lean_Meta_Grind_simpExists___redArg___closed__10;
                    v___x_5410_ = l_Lean_mkConst(v___x_5409_, v_u_5408_);
                    v___x_5411_ = l_Lean_mkApp3(v___x_5410_, v_arg_5316_, v_p_5405_, v___y_5388_);
                    v___x_5412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5412_, 0, v___x_5411_);
                    v___x_5413_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_5413_, 0, v_expr_5407_);
                    crate::leanh::lean_ctor_set(v___x_5413_, 1, v___x_5412_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_5413_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_5319_,
                    );
                    v___x_5414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5414_, 0, v___x_5413_);
                    v___x_5415_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5415_, 0, v___x_5414_);
                    return v___x_5415_;
                }
            }
            15 => {
                if v___y_5417_ == 0 {
                    crate::leanh::lean_dec(v_binderName_5320_);
                    v___y_5323_ = v_a_5300_;
                    v___y_5324_ = v_a_5301_;
                    v___y_5325_ = v_a_5302_;
                    v___y_5326_ = v_a_5303_;
                    state = 3;
                    continue;
                } else {
                    v___x_5418_ = l_Lean_Expr_appFn_x21(v_body_5321_);
                    v___x_5419_ = l_Lean_Expr_appFn_x21(v___x_5418_);
                    if crate::leanh::lean_obj_tag(v___x_5419_) == 4 {
                        v_declName_5420_ = crate::leanh::lean_ctor_get(v___x_5419_, 0);
                        crate::leanh::lean_inc(v_declName_5420_);
                        crate::leanh::lean_dec_ref_known(v___x_5419_, 2);
                        v___x_5421_ = l_Lean_Meta_Grind_simpForall___closed__2;
                        v___x_5422_ = lean_name_eq(v_declName_5420_, v___x_5421_);
                        if v___x_5422_ == 0 {
                            v___x_5423_ = l_Lean_Meta_Grind_simpForall___closed__4;
                            v___x_5424_ = lean_name_eq(v_declName_5420_, v___x_5423_);
                            crate::leanh::lean_dec(v_declName_5420_);
                            if v___x_5424_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5418_);
                                crate::leanh::lean_dec(v_binderName_5320_);
                                v___y_5323_ = v_a_5300_;
                                v___y_5324_ = v_a_5301_;
                                v___y_5325_ = v_a_5302_;
                                v___y_5326_ = v_a_5303_;
                                state = 3;
                                continue;
                            } else {
                                v_b_5425_ = l_Lean_Expr_appArg_x21(v___x_5418_);
                                crate::leanh::lean_dec_ref(v___x_5418_);
                                v_b_5426_ = l_Lean_Expr_appArg_x21(v_body_5321_);
                                v___x_5427_ = l_Lean_Expr_hasLooseBVars(v_b_5425_);
                                if v___x_5427_ == 0 {
                                    v___y_5387_ = v___x_5424_;
                                    v___y_5388_ = v_b_5425_;
                                    v___y_5389_ = v_b_5426_;
                                    v___y_5390_ = v___x_5424_;
                                    state = 14;
                                    continue;
                                } else {
                                    v___y_5387_ = v___x_5424_;
                                    v___y_5388_ = v_b_5425_;
                                    v___y_5389_ = v_b_5426_;
                                    v___y_5390_ = v___x_5422_;
                                    state = 14;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_declName_5420_);
                            v_pRaw_5428_ = l_Lean_Expr_appArg_x21(v___x_5418_);
                            crate::leanh::lean_dec_ref(v___x_5418_);
                            v_qRaw_5429_ = l_Lean_Expr_appArg_x21(v_body_5321_);
                            crate::leanh::lean_dec_ref(v_body_5321_);
                            v___x_5430_ = 0;
                            crate::leanh::lean_inc_ref_n(v_arg_5316_, 4);
                            crate::leanh::lean_inc(v_binderName_5320_);
                            v_p_5431_ = l_Lean_mkLambda(
                                v_binderName_5320_,
                                v___x_5430_,
                                v_arg_5316_,
                                v_pRaw_5428_,
                            );
                            v_q_5432_ = l_Lean_mkLambda(
                                v_binderName_5320_,
                                v___x_5430_,
                                v_arg_5316_,
                                v_qRaw_5429_,
                            );
                            v_u_5433_ = l_Lean_Expr_constLevels_x21(v___x_5317_);
                            crate::leanh::lean_inc_ref(v_p_5431_);
                            crate::leanh::lean_inc_ref(v___x_5317_);
                            v___x_5434_ = l_Lean_mkAppB(v___x_5317_, v_arg_5316_, v_p_5431_);
                            crate::leanh::lean_inc_ref(v_q_5432_);
                            v___x_5435_ = l_Lean_mkAppB(v___x_5317_, v_arg_5316_, v_q_5432_);
                            v_expr_5436_ = l_Lean_mkOr(v___x_5434_, v___x_5435_);
                            v___x_5437_ = l_Lean_Meta_Grind_simpExists___redArg___closed__12;
                            v___x_5438_ = l_Lean_mkConst(v___x_5437_, v_u_5433_);
                            v___x_5439_ =
                                l_Lean_mkApp3(v___x_5438_, v_arg_5316_, v_p_5431_, v_q_5432_);
                            v___x_5440_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5440_, 0, v___x_5439_);
                            v___x_5441_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_5441_, 0, v_expr_5436_);
                            crate::leanh::lean_ctor_set(v___x_5441_, 1, v___x_5440_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_5441_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_5319_,
                            );
                            v___x_5442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5442_, 0, v___x_5441_);
                            v___x_5443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5443_, 0, v___x_5442_);
                            return v___x_5443_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5419_);
                        crate::leanh::lean_dec_ref(v___x_5418_);
                        crate::leanh::lean_dec_ref(v_body_5321_);
                        crate::leanh::lean_dec(v_binderName_5320_);
                        crate::leanh::lean_dec_ref(v___x_5317_);
                        crate::leanh::lean_dec_ref(v_arg_5316_);
                        v___x_5444_ = l_Lean_Meta_Grind_simpForall___closed__0;
                        v___x_5445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5445_, 0, v___x_5444_);
                        return v___x_5445_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpExists___redArg___boxed(
    mut v_e_5452_: *mut crate::leanh::LeanObject,
    mut v_a_5453_: *mut crate::leanh::LeanObject,
    mut v_a_5454_: *mut crate::leanh::LeanObject,
    mut v_a_5455_: *mut crate::leanh::LeanObject,
    mut v_a_5456_: *mut crate::leanh::LeanObject,
    mut v_a_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5458_ = l_Lean_Meta_Grind_simpExists___redArg(
        v_e_5452_, v_a_5453_, v_a_5454_, v_a_5455_, v_a_5456_,
    );
    crate::leanh::lean_dec(v_a_5456_);
    crate::leanh::lean_dec_ref(v_a_5455_);
    crate::leanh::lean_dec(v_a_5454_);
    crate::leanh::lean_dec_ref(v_a_5453_);
    return v_res_5458_;
}
pub unsafe fn l_Lean_Meta_Grind_simpExists(
    mut v_e_5459_: *mut crate::leanh::LeanObject,
    mut v_a_5460_: *mut crate::leanh::LeanObject,
    mut v_a_5461_: *mut crate::leanh::LeanObject,
    mut v_a_5462_: *mut crate::leanh::LeanObject,
    mut v_a_5463_: *mut crate::leanh::LeanObject,
    mut v_a_5464_: *mut crate::leanh::LeanObject,
    mut v_a_5465_: *mut crate::leanh::LeanObject,
    mut v_a_5466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5468_ = l_Lean_Meta_Grind_simpExists___redArg(
        v_e_5459_, v_a_5463_, v_a_5464_, v_a_5465_, v_a_5466_,
    );
    return v___x_5468_;
}
pub unsafe fn l_Lean_Meta_Grind_simpExists___boxed(
    mut v_e_5469_: *mut crate::leanh::LeanObject,
    mut v_a_5470_: *mut crate::leanh::LeanObject,
    mut v_a_5471_: *mut crate::leanh::LeanObject,
    mut v_a_5472_: *mut crate::leanh::LeanObject,
    mut v_a_5473_: *mut crate::leanh::LeanObject,
    mut v_a_5474_: *mut crate::leanh::LeanObject,
    mut v_a_5475_: *mut crate::leanh::LeanObject,
    mut v_a_5476_: *mut crate::leanh::LeanObject,
    mut v_a_5477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5478_ = l_Lean_Meta_Grind_simpExists(
        v_e_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_, v_a_5474_, v_a_5475_, v_a_5476_,
    );
    crate::leanh::lean_dec(v_a_5476_);
    crate::leanh::lean_dec_ref(v_a_5475_);
    crate::leanh::lean_dec(v_a_5474_);
    crate::leanh::lean_dec_ref(v_a_5473_);
    crate::leanh::lean_dec(v_a_5472_);
    crate::leanh::lean_dec_ref(v_a_5471_);
    crate::leanh::lean_dec(v_a_5470_);
    return v_res_5478_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5496_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
    v___x_5497_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
    v___x_5498_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_simpExists___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5499_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_5496_, v___x_5497_, v___x_5498_);
    return v___x_5499_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10____boxed(
    mut v_a_5500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5501_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
    return v_res_5501_;
}
pub unsafe fn l_Lean_Meta_Grind_addForallSimproc(
    mut v_s_5502_: *mut crate::leanh::LeanObject,
    mut v_a_5503_: *mut crate::leanh::LeanObject,
    mut v_a_5504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: u8 = 0;
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5506_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
    v___x_5507_ = 1;
    v___x_5508_ =
        l_Lean_Meta_Simp_Simprocs_add(v_s_5502_, v___x_5506_, v___x_5507_, v_a_5503_, v_a_5504_);
    if crate::leanh::lean_obj_tag(v___x_5508_) == 0 {
        let mut v_a_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5509_ = crate::leanh::lean_ctor_get(v___x_5508_, 0);
        crate::leanh::lean_inc(v_a_5509_);
        crate::leanh::lean_dec_ref_known(v___x_5508_, 1);
        v___x_5510_ = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
        v___x_5511_ = l_Lean_Meta_Simp_Simprocs_add(
            v_a_5509_,
            v___x_5510_,
            v___x_5507_,
            v_a_5503_,
            v_a_5504_,
        );
        return v___x_5511_;
    } else {
        return v___x_5508_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_addForallSimproc___boxed(
    mut v_s_5512_: *mut crate::leanh::LeanObject,
    mut v_a_5513_: *mut crate::leanh::LeanObject,
    mut v_a_5514_: *mut crate::leanh::LeanObject,
    mut v_a_5515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5516_ = l_Lean_Meta_Grind_addForallSimproc(v_s_5512_, v_a_5513_, v_a_5514_);
    crate::leanh::lean_dec(v_a_5514_);
    crate::leanh::lean_dec_ref(v_a_5513_);
    return v_res_5516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_1871237267____hygCtx___hyg_8_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__35_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__40_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_ForallProp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_ForallProp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Grind_Propagator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
}
