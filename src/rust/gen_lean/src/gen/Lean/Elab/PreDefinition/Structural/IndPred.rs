// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.IndPred
// Imports: Lean.Elab.PreDefinition.Structural.Basic Lean.Elab.PreDefinition.Structural.RecArgInfo Lean.Util.HasConstCache Lean.Meta.IndPredBelow Init.Omega
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_Lean_Name_append, l_Lean_replaceRef, l_List_lengthTR___redArg,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AuxRecursor::l_Lean_isCasesOnRecursor;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_getPrefix,
    l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numCtors;
use crate::r#gen::Lean::Elab::PreDefinition::Basic::l_Lean_Elab_ensureNoRecFn;
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::l_Lean_Elab_FixedParamPerm_isFixed;
use crate::r#gen::Lean::Elab::PreDefinition::Structural::Basic::{
    initialize_Lean_Elab_PreDefinition_Structural_Basic,
    l_Lean_Elab_Structural_recArgHasLooseBVarsAt,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::RecArgInfo::{
    initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo,
    l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor,
    l_Lean_Elab_Structural_instInhabitedRecArgInfo_default,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo,
};
use crate::r#gen::Lean::Elab::RecAppSyntax::l_Lean_getRecAppSyntax_x3f;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_constName_x21,
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getForallBody, l_Lean_Expr_headBeta, l_Lean_Expr_isApp,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkAppN,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instMonadMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__1___boxed,
    l_Lean_Meta_instantiateForall, l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
    l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::IndPredBelow::{
    initialize_Lean_Meta_IndPredBelow, l_Lean_Meta_IndPredBelow_mkBelowMatcher,
    runtime_initialize_Lean_Meta_IndPredBelow,
};
use crate::r#gen::Lean::Meta::Match::MatcherApp::Basic::l_Lean_Meta_MatcherApp_toExpr;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_Extension_getMatcherInfo_x3f, l_Lean_Meta_Match_MatcherInfo_arity,
    l_Lean_Meta_Match_MatcherInfo_getMotivePos, l_Lean_Meta_Match_MatcherInfo_numAlts,
    l_Lean_Meta_Match_instInhabitedAltParamInfo_default,
};
use crate::r#gen::Lean::Meta::WHNF::l_Lean_Meta_whnfCore;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::HasConstCache::{
    initialize_Lean_Util_HasConstCache, l_Lean_HasConstCache_containsUnsafe,
    runtime_initialize_Lean_Util_HasConstCache,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0_value) as *mut crate::leanh::LeanObject,9743492140944907313 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0_value: crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [105, 110, 115, 117, 102, 102, 105, 99, 105, 101, 110, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 116, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__0_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__1_value: crate::leanh::LeanStringObject<27> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 97, 116, 99, 104, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1_value) as *mut crate::leanh::LeanObject,6897119537390546559 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2_value) as *mut crate::leanh::LeanObject,14406337792964512117 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [109, 97, 116, 99, 104, 101, 114, 65, 112, 112, 32, 98, 101, 102, 111, 114, 101, 32, 97, 100, 100, 105, 110, 103, 32, 98, 101, 108, 111, 119, 32, 116, 114, 97, 110, 115, 102, 111, 114, 109, 97, 116, 105, 111, 110, 58, 10, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 117, 110, 84, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0_value) as *mut crate::leanh::LeanObject,11438940029995117633 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj(
    mut v_i_2878_: *mut crate::leanh::LeanObject,
    mut v_n_2879_: *mut crate::leanh::LeanObject,
    mut v_e_2880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2882_: u8 = 0;
    let mut v_isZero_2883_: u8 = 0;
    let mut v_one_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2889_: u8 = 0;
    let mut v_one_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2881_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2882_ = lean_nat_dec_eq(v_i_2878_, v_zero_2881_);
                if v_isZero_2882_ == 1 {
                    crate::leanh::lean_dec(v_i_2878_);
                    v_isZero_2883_ = lean_nat_dec_eq(v_n_2879_, v_zero_2881_);
                    if v_isZero_2883_ == 0 {
                        v_one_2884_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_2885_ = lean_nat_sub(v_n_2879_, v_one_2884_);
                        crate::leanh::lean_dec(v_n_2879_);
                        v___x_2886_ = lean_nat_dec_eq(v_n_2885_, v_zero_2881_);
                        crate::leanh::lean_dec(v_n_2885_);
                        if v___x_2886_ == 0 {
                            v___x_2887_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1;
                            v___x_2888_ =
                                l_Lean_Expr_proj___override(v___x_2887_, v_zero_2881_, v_e_2880_);
                            return v___x_2888_;
                        } else {
                            return v_e_2880_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_n_2879_);
                        return v_e_2880_;
                    }
                } else {
                    v_isZero_2889_ = lean_nat_dec_eq(v_n_2879_, v_zero_2881_);
                    if v_isZero_2889_ == 0 {
                        v_one_2890_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_2891_ = lean_nat_sub(v_i_2878_, v_one_2890_);
                        crate::leanh::lean_dec(v_i_2878_);
                        v_n_2892_ = lean_nat_sub(v_n_2879_, v_one_2890_);
                        crate::leanh::lean_dec(v_n_2879_);
                        v___x_2893_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1;
                        v___x_2894_ =
                            l_Lean_Expr_proj___override(v___x_2893_, v_one_2890_, v_e_2880_);
                        v_i_2878_ = v_n_2891_;
                        v_n_2879_ = v_n_2892_;
                        v_e_2880_ = v___x_2894_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_2879_);
                        crate::leanh::lean_dec(v_i_2878_);
                        return v_e_2880_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(
    mut v_t_2896_: *mut crate::leanh::LeanObject,
    mut v_k_2897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2896_) == 0 {
                    v_k_2898_ = crate::leanh::lean_ctor_get(v_t_2896_, 1);
                    v_v_2899_ = crate::leanh::lean_ctor_get(v_t_2896_, 2);
                    v_l_2900_ = crate::leanh::lean_ctor_get(v_t_2896_, 3);
                    v_r_2901_ = crate::leanh::lean_ctor_get(v_t_2896_, 4);
                    v___x_2902_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2897_, v_k_2898_);
                    match v___x_2902_ {
                        0 => {
                            v_t_2896_ = v_l_2900_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_2899_);
                            v___x_2904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2904_, 0, v_v_2899_);
                            return v___x_2904_;
                        }
                        _ => {
                            v_t_2896_ = v_r_2901_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2906_ = crate::leanh::lean_box(0);
                    return v___x_2906_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg___boxed(
    mut v_t_2907_: *mut crate::leanh::LeanObject,
    mut v_k_2908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2909_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(v_t_2907_, v_k_2908_);
    crate::leanh::lean_dec(v_k_2908_);
    crate::leanh::lean_dec(v_t_2907_);
    return v_res_2909_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4(
    mut v_xs_2910_: *mut crate::leanh::LeanObject,
    mut v_v_2911_: *mut crate::leanh::LeanObject,
    mut v_i_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: u8 = 0;
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2913_ = lean_array_get_size(v_xs_2910_);
                v___x_2914_ = lean_nat_dec_lt(v_i_2912_, v___x_2913_);
                if v___x_2914_ == 0 {
                    crate::leanh::lean_dec(v_i_2912_);
                    v___x_2915_ = crate::leanh::lean_box(0);
                    return v___x_2915_;
                } else {
                    v___x_2916_ = lean_array_fget_borrowed(v_xs_2910_, v_i_2912_);
                    v___x_2917_ = lean_nat_dec_eq(v___x_2916_, v_v_2911_);
                    if v___x_2917_ == 0 {
                        v___x_2918_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2919_ = lean_nat_add(v_i_2912_, v___x_2918_);
                        crate::leanh::lean_dec(v_i_2912_);
                        v_i_2912_ = v___x_2919_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2921_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2921_, 0, v_i_2912_);
                        return v___x_2921_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4___boxed(
    mut v_xs_2922_: *mut crate::leanh::LeanObject,
    mut v_v_2923_: *mut crate::leanh::LeanObject,
    mut v_i_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2925_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4(v_xs_2922_, v_v_2923_, v_i_2924_);
    crate::leanh::lean_dec(v_v_2923_);
    crate::leanh::lean_dec_ref(v_xs_2922_);
    return v_res_2925_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3(
    mut v_xs_2926_: *mut crate::leanh::LeanObject,
    mut v_v_2927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2928_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2929_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4(v_xs_2926_, v_v_2927_, v___x_2928_);
    return v___x_2929_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3___boxed(
    mut v_xs_2930_: *mut crate::leanh::LeanObject,
    mut v_v_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3(v_xs_2930_, v_v_2931_);
    crate::leanh::lean_dec(v_v_2931_);
    crate::leanh::lean_dec_ref(v_xs_2930_);
    return v_res_2932_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2(
    mut v_xs_2933_: *mut crate::leanh::LeanObject,
    mut v_v_2934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2935_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3(v_xs_2933_, v_v_2934_);
                if crate::leanh::lean_obj_tag(v___x_2935_) == 0 {
                    v___x_2936_ = crate::leanh::lean_box(0);
                    return v___x_2936_;
                } else {
                    v_val_2937_ = crate::leanh::lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2944_ = (!crate::leanh::lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2944_ == 0 {
                        v___x_2939_ = v___x_2935_;
                        v_isShared_2940_ = v_isSharedCheck_2944_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2937_);
                        crate::leanh::lean_dec(v___x_2935_);
                        v___x_2939_ = crate::leanh::lean_box(0);
                        v_isShared_2940_ = v_isSharedCheck_2944_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2940_ == 0 {
                    v___x_2942_ = v___x_2939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_val_2937_);
                    v___x_2942_ = v_reuseFailAlloc_2943_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2942_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2___boxed(
    mut v_xs_2945_: *mut crate::leanh::LeanObject,
    mut v_v_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2947_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2(v_xs_2945_, v_v_2946_);
    crate::leanh::lean_dec(v_v_2946_);
    crate::leanh::lean_dec_ref(v_xs_2945_);
    return v_res_2947_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3_spec__5(
    mut v_a_2948_: *mut crate::leanh::LeanObject,
    mut v_as_2949_: *mut crate::leanh::LeanObject,
    mut v_i_2950_: usize,
    mut v_stop_2951_: usize,
) -> u8 {
    let mut v___x_2952_: u8 = 0;
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: u8 = 0;
    let mut v___x_2955_: usize = 0;
    let mut v___x_2956_: usize = 0;
    let mut v___x_2958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2952_ = lean_usize_dec_eq(v_i_2950_, v_stop_2951_);
                if v___x_2952_ == 0 {
                    v___x_2953_ = lean_array_uget_borrowed(v_as_2949_, v_i_2950_);
                    v___x_2954_ = lean_nat_dec_eq(v_a_2948_, v___x_2953_);
                    if v___x_2954_ == 0 {
                        v___x_2955_ = 1usize;
                        v___x_2956_ = lean_usize_add(v_i_2950_, v___x_2955_);
                        v_i_2950_ = v___x_2956_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2954_;
                    }
                } else {
                    v___x_2958_ = 0;
                    return v___x_2958_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3_spec__5___boxed(
    mut v_a_2959_: *mut crate::leanh::LeanObject,
    mut v_as_2960_: *mut crate::leanh::LeanObject,
    mut v_i_2961_: *mut crate::leanh::LeanObject,
    mut v_stop_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2963_: usize = 0;
    let mut v_stop_boxed_2964_: usize = 0;
    let mut v_res_2965_: u8 = 0;
    let mut v_r_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2963_ = crate::leanh::lean_unbox_usize(v_i_2961_);
    crate::leanh::lean_dec(v_i_2961_);
    v_stop_boxed_2964_ = crate::leanh::lean_unbox_usize(v_stop_2962_);
    crate::leanh::lean_dec(v_stop_2962_);
    v_res_2965_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3_spec__5(v_a_2959_, v_as_2960_, v_i_boxed_2963_, v_stop_boxed_2964_);
    crate::leanh::lean_dec_ref(v_as_2960_);
    crate::leanh::lean_dec(v_a_2959_);
    v_r_2966_ = crate::leanh::lean_box((v_res_2965_) as usize);
    return v_r_2966_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3(
    mut v_as_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    v___x_2969_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2970_ = lean_array_get_size(v_as_2967_);
    v___x_2971_ = lean_nat_dec_lt(v___x_2969_, v___x_2970_);
    if v___x_2971_ == 0 {
        return v___x_2971_;
    } else {
        if v___x_2971_ == 0 {
            return v___x_2971_;
        } else {
            let mut v___x_2972_: usize = 0;
            let mut v___x_2973_: usize = 0;
            let mut v___x_2974_: u8 = 0;
            v___x_2972_ = 0usize;
            v___x_2973_ = lean_usize_of_nat(v___x_2970_);
            v___x_2974_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3_spec__5(v_a_2968_, v_as_2967_, v___x_2972_, v___x_2973_);
            return v___x_2974_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3___boxed(
    mut v_as_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2977_: u8 = 0;
    let mut v_r_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3(v_as_2975_, v_a_2976_);
    crate::leanh::lean_dec(v_a_2976_);
    crate::leanh::lean_dec_ref(v_as_2975_);
    v_r_2978_ = crate::leanh::lean_box((v_res_2977_) as usize);
    return v_r_2978_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(
    mut v_recArgInfo_2979_: *mut crate::leanh::LeanObject,
    mut v_args_2980_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2981_: *mut crate::leanh::LeanObject,
    mut v___x_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
    mut v_b_2984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedParamPerm_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: u8 = 0;
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    let mut v___x_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_nat_dec_lt(v_a_2983_, v_upperBound_2981_);
                if v___x_2991_ == 0 {
                    crate::leanh::lean_dec(v_a_2983_);
                    v___x_2992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2992_, 0, v_b_2984_);
                    return v___x_2992_;
                } else {
                    v_fixedParamPerm_2993_ = crate::leanh::lean_ctor_get(v_recArgInfo_2979_, 1);
                    v_indicesPos_2994_ = crate::leanh::lean_ctor_get(v_recArgInfo_2979_, 3);
                    v___x_3000_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3(v_indicesPos_2994_, v_a_2983_);
                    if v___x_3000_ == 0 {
                        v___x_3001_ = lean_nat_dec_eq(v_a_2983_, v___x_2982_);
                        v___y_2996_ = v___x_3001_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2996_ = v___x_3000_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2988_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2989_ = lean_nat_add(v_a_2983_, v___x_2988_);
                crate::leanh::lean_dec(v_a_2983_);
                v_a_2983_ = v___x_2989_;
                v_b_2984_ = v_a_2987_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2996_ == 0 {
                    v___x_2997_ =
                        l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_2993_, v_a_2983_);
                    if v___x_2997_ == 0 {
                        v___x_2998_ = lean_array_fget_borrowed(v_args_2980_, v_a_2983_);
                        crate::leanh::lean_inc(v___x_2998_);
                        v___x_2999_ = lean_array_push(v_b_2984_, v___x_2998_);
                        v_a_2987_ = v___x_2999_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2987_ = v_b_2984_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2987_ = v_b_2984_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg___boxed(
    mut v_recArgInfo_3002_: *mut crate::leanh::LeanObject,
    mut v_args_3003_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3004_: *mut crate::leanh::LeanObject,
    mut v___x_3005_: *mut crate::leanh::LeanObject,
    mut v_a_3006_: *mut crate::leanh::LeanObject,
    mut v_b_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(v_recArgInfo_3002_, v_args_3003_, v_upperBound_3004_, v___x_3005_, v_a_3006_, v_b_3007_);
    crate::leanh::lean_dec(v___x_3005_);
    crate::leanh::lean_dec(v_upperBound_3004_);
    crate::leanh::lean_dec_ref(v_args_3003_);
    crate::leanh::lean_dec_ref(v_recArgInfo_3002_);
    return v_res_3009_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(
    mut v_msgData_3010_: *mut crate::leanh::LeanObject,
    mut v___y_3011_: *mut crate::leanh::LeanObject,
    mut v___y_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3016_ = lean_st_ref_get(v___y_3014_);
    v_env_3017_ = crate::leanh::lean_ctor_get(v___x_3016_, 0);
    crate::leanh::lean_inc_ref(v_env_3017_);
    crate::leanh::lean_dec(v___x_3016_);
    v___x_3018_ = lean_st_ref_get(v___y_3012_);
    v_mctx_3019_ = crate::leanh::lean_ctor_get(v___x_3018_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3019_);
    crate::leanh::lean_dec(v___x_3018_);
    v_lctx_3020_ = crate::leanh::lean_ctor_get(v___y_3011_, 2);
    v_options_3021_ = crate::leanh::lean_ctor_get(v___y_3013_, 2);
    crate::leanh::lean_inc_ref(v_options_3021_);
    crate::leanh::lean_inc_ref(v_lctx_3020_);
    v___x_3022_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3022_, 0, v_env_3017_);
    crate::leanh::lean_ctor_set(v___x_3022_, 1, v_mctx_3019_);
    crate::leanh::lean_ctor_set(v___x_3022_, 2, v_lctx_3020_);
    crate::leanh::lean_ctor_set(v___x_3022_, 3, v_options_3021_);
    v___x_3023_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3023_, 0, v___x_3022_);
    crate::leanh::lean_ctor_set(v___x_3023_, 1, v_msgData_3010_);
    v___x_3024_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3024_, 0, v___x_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0___boxed(
    mut v_msgData_3025_: *mut crate::leanh::LeanObject,
    mut v___y_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
    mut v___y_3029_: *mut crate::leanh::LeanObject,
    mut v___y_3030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msgData_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
    crate::leanh::lean_dec(v___y_3029_);
    crate::leanh::lean_dec_ref(v___y_3028_);
    crate::leanh::lean_dec(v___y_3027_);
    crate::leanh::lean_dec_ref(v___y_3026_);
    return v_res_3031_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(
    mut v_msg_3032_: *mut crate::leanh::LeanObject,
    mut v___y_3033_: *mut crate::leanh::LeanObject,
    mut v___y_3034_: *mut crate::leanh::LeanObject,
    mut v___y_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3038_ = crate::leanh::lean_ctor_get(v___y_3035_, 5);
                v___x_3039_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msg_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
                v_a_3040_ = crate::leanh::lean_ctor_get(v___x_3039_, 0);
                v_isSharedCheck_3048_ = (!crate::leanh::lean_is_exclusive(v___x_3039_)) as u8;
                if v_isSharedCheck_3048_ == 0 {
                    v___x_3042_ = v___x_3039_;
                    v_isShared_3043_ = v_isSharedCheck_3048_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3040_);
                    crate::leanh::lean_dec(v___x_3039_);
                    v___x_3042_ = crate::leanh::lean_box(0);
                    v_isShared_3043_ = v_isSharedCheck_3048_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3038_);
                v___x_3044_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3044_, 0, v_ref_3038_);
                crate::leanh::lean_ctor_set(v___x_3044_, 1, v_a_3040_);
                if v_isShared_3043_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3042_, 1);
                    crate::leanh::lean_ctor_set(v___x_3042_, 0, v___x_3044_);
                    v___x_3046_ = v___x_3042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
                    v___x_3046_ = v_reuseFailAlloc_3047_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3046_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg___boxed(
    mut v_msg_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
    mut v___y_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3055_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v_msg_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
    crate::leanh::lean_dec(v___y_3053_);
    crate::leanh::lean_dec_ref(v___y_3052_);
    crate::leanh::lean_dec(v___y_3051_);
    crate::leanh::lean_dec_ref(v___y_3050_);
    return v_res_3055_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3057_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0;
    v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
    return v___x_3058_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3060_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2;
    v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
    return v___x_3061_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3062_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_3062_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3065_ = crate::leanh::lean_box(0);
    v_dummy_3066_ = l_Lean_Expr_sort___override(v___x_3065_);
    return v_dummy_3066_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp(
    mut v_recArgInfo_3067_: *mut crate::leanh::LeanObject,
    mut v_ctx_3068_: *mut crate::leanh::LeanObject,
    mut v_fidx_3069_: *mut crate::leanh::LeanObject,
    mut v_positions_3070_: *mut crate::leanh::LeanObject,
    mut v_e_3071_: *mut crate::leanh::LeanObject,
    mut v_args_3072_: *mut crate::leanh::LeanObject,
    mut v_a_3073_: *mut crate::leanh::LeanObject,
    mut v_a_3074_: *mut crate::leanh::LeanObject,
    mut v_a_3075_: *mut crate::leanh::LeanObject,
    mut v_a_3076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recArgPos_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motives_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3114_: u8 = 0;
    let mut v_nargs_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3128_: u8 = 0;
    let mut v_a_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3132_: u8 = 0;
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_recArgPos_3078_ = crate::leanh::lean_ctor_get(v_recArgInfo_3067_, 2);
                v___x_3079_ = lean_array_get_size(v_args_3072_);
                v___x_3080_ = lean_nat_dec_lt(v_recArgPos_3078_, v___x_3079_);
                if v___x_3080_ == 0 {
                    v___x_3081_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1);
                    v___x_3082_ = l_Lean_indentExpr(v_e_3071_);
                    v___x_3083_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3083_, 0, v___x_3081_);
                    crate::leanh::lean_ctor_set(v___x_3083_, 1, v___x_3082_);
                    v___x_3084_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v___x_3083_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
                    return v___x_3084_;
                } else {
                    v___x_3085_ = lean_array_fget_borrowed(v_args_3072_, v_recArgPos_3078_);
                    crate::leanh::lean_inc(v___x_3085_);
                    v___x_3086_ = l_Lean_Meta_whnfCore(
                        v___x_3085_,
                        v_a_3073_,
                        v_a_3074_,
                        v_a_3075_,
                        v_a_3076_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3086_) == 0 {
                        v_a_3087_ = crate::leanh::lean_ctor_get(v___x_3086_, 0);
                        crate::leanh::lean_inc(v_a_3087_);
                        crate::leanh::lean_dec_ref_known(v___x_3086_, 1);
                        v___x_3097_ = l_Lean_Expr_getAppFn(v_a_3087_);
                        if crate::leanh::lean_obj_tag(v___x_3097_) == 1 {
                            v_fvarId_3098_ = crate::leanh::lean_ctor_get(v___x_3097_, 0);
                            crate::leanh::lean_inc(v_fvarId_3098_);
                            crate::leanh::lean_dec_ref_known(v___x_3097_, 1);
                            v_motives_3099_ = crate::leanh::lean_ctor_get(v_ctx_3068_, 1);
                            v___x_3100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(v_motives_3099_, v_fvarId_3098_);
                            crate::leanh::lean_dec(v_fvarId_3098_);
                            if crate::leanh::lean_obj_tag(v___x_3100_) == 1 {
                                v_val_3101_ = crate::leanh::lean_ctor_get(v___x_3100_, 0);
                                crate::leanh::lean_inc(v_val_3101_);
                                crate::leanh::lean_dec_ref_known(v___x_3100_, 1);
                                v_fst_3102_ = crate::leanh::lean_ctor_get(v_val_3101_, 0);
                                crate::leanh::lean_inc(v_fst_3102_);
                                v_snd_3103_ = crate::leanh::lean_ctor_get(v_val_3101_, 1);
                                crate::leanh::lean_inc(v_snd_3103_);
                                crate::leanh::lean_dec(v_val_3101_);
                                v___x_3104_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4);
                                v___x_3105_ = lean_array_get_borrowed(
                                    v___x_3104_,
                                    v_positions_3070_,
                                    v_fst_3102_,
                                );
                                crate::leanh::lean_dec(v_fst_3102_);
                                v___x_3106_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2(v___x_3105_, v_fidx_3069_);
                                if crate::leanh::lean_obj_tag(v___x_3106_) == 1 {
                                    crate::leanh::lean_dec_ref(v_e_3071_);
                                    v_val_3107_ = crate::leanh::lean_ctor_get(v___x_3106_, 0);
                                    crate::leanh::lean_inc(v_val_3107_);
                                    crate::leanh::lean_dec_ref_known(v___x_3106_, 1);
                                    v___x_3108_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_3109_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5;
                                    v___x_3110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(v_recArgInfo_3067_, v_args_3072_, v___x_3079_, v_recArgPos_3078_, v___x_3108_, v___x_3109_);
                                    if crate::leanh::lean_obj_tag(v___x_3110_) == 0 {
                                        v_a_3111_ = crate::leanh::lean_ctor_get(v___x_3110_, 0);
                                        v_isSharedCheck_3128_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3110_)) as u8;
                                        if v_isSharedCheck_3128_ == 0 {
                                            v___x_3113_ = v___x_3110_;
                                            v_isShared_3114_ = v_isSharedCheck_3128_;
                                            state = 2;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3111_);
                                            crate::leanh::lean_dec(v___x_3110_);
                                            v___x_3113_ = crate::leanh::lean_box(0);
                                            v_isShared_3114_ = v_isSharedCheck_3128_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_val_3107_);
                                        crate::leanh::lean_dec(v_snd_3103_);
                                        crate::leanh::lean_dec(v_a_3087_);
                                        v_a_3129_ = crate::leanh::lean_ctor_get(v___x_3110_, 0);
                                        v_isSharedCheck_3136_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3110_)) as u8;
                                        if v_isSharedCheck_3136_ == 0 {
                                            v___x_3131_ = v___x_3110_;
                                            v_isShared_3132_ = v_isSharedCheck_3136_;
                                            state = 4;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3129_);
                                            crate::leanh::lean_dec(v___x_3110_);
                                            v___x_3131_ = crate::leanh::lean_box(0);
                                            v_isShared_3132_ = v_isSharedCheck_3136_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_3106_);
                                    crate::leanh::lean_dec(v_snd_3103_);
                                    crate::leanh::lean_dec(v_a_3087_);
                                    v___y_3089_ = v_a_3073_;
                                    v___y_3090_ = v_a_3074_;
                                    v___y_3091_ = v_a_3075_;
                                    v___y_3092_ = v_a_3076_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_3100_);
                                crate::leanh::lean_dec(v_a_3087_);
                                v___y_3089_ = v_a_3073_;
                                v___y_3090_ = v_a_3074_;
                                v___y_3091_ = v_a_3075_;
                                v___y_3092_ = v_a_3076_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3097_);
                            crate::leanh::lean_dec(v_a_3087_);
                            v___y_3089_ = v_a_3073_;
                            v___y_3090_ = v_a_3074_;
                            v___y_3091_ = v_a_3075_;
                            v___y_3092_ = v_a_3076_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3071_);
                        return v___x_3086_;
                    }
                }
            }
            1 => {
                v___x_3093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3);
                v___x_3094_ = l_Lean_indentExpr(v_e_3071_);
                v___x_3095_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3095_, 0, v___x_3093_);
                crate::leanh::lean_ctor_set(v___x_3095_, 1, v___x_3094_);
                v___x_3096_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v___x_3095_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
                return v___x_3096_;
            }
            2 => {
                v_nargs_3115_ = l_Lean_Expr_getAppNumArgs(v_a_3087_);
                v_dummy_3116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                crate::leanh::lean_inc(v_nargs_3115_);
                v___x_3117_ = lean_mk_array(v_nargs_3115_, v_dummy_3116_);
                v___x_3118_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3119_ = lean_nat_sub(v_nargs_3115_, v___x_3118_);
                crate::leanh::lean_dec(v_nargs_3115_);
                v___x_3120_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_3087_,
                    v___x_3117_,
                    v___x_3119_,
                );
                v___x_3121_ = l_Lean_mkAppN(v_snd_3103_, v___x_3120_);
                crate::leanh::lean_dec_ref(v___x_3120_);
                v___x_3122_ = lean_array_get_size(v___x_3105_);
                v___x_3123_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj(v_val_3107_, v___x_3122_, v___x_3121_);
                v___x_3124_ = l_Lean_mkAppN(v___x_3123_, v_a_3111_);
                crate::leanh::lean_dec(v_a_3111_);
                if v_isShared_3114_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3113_, 0, v___x_3124_);
                    v___x_3126_ = v___x_3113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3127_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
                    v___x_3126_ = v_reuseFailAlloc_3127_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3126_;
            }
            4 => {
                if v_isShared_3132_ == 0 {
                    v___x_3134_ = v___x_3131_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
                    v___x_3134_ = v_reuseFailAlloc_3135_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___boxed(
    mut v_recArgInfo_3137_: *mut crate::leanh::LeanObject,
    mut v_ctx_3138_: *mut crate::leanh::LeanObject,
    mut v_fidx_3139_: *mut crate::leanh::LeanObject,
    mut v_positions_3140_: *mut crate::leanh::LeanObject,
    mut v_e_3141_: *mut crate::leanh::LeanObject,
    mut v_args_3142_: *mut crate::leanh::LeanObject,
    mut v_a_3143_: *mut crate::leanh::LeanObject,
    mut v_a_3144_: *mut crate::leanh::LeanObject,
    mut v_a_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp(v_recArgInfo_3137_, v_ctx_3138_, v_fidx_3139_, v_positions_3140_, v_e_3141_, v_args_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
    crate::leanh::lean_dec(v_a_3146_);
    crate::leanh::lean_dec_ref(v_a_3145_);
    crate::leanh::lean_dec(v_a_3144_);
    crate::leanh::lean_dec_ref(v_a_3143_);
    crate::leanh::lean_dec_ref(v_args_3142_);
    crate::leanh::lean_dec_ref(v_positions_3140_);
    crate::leanh::lean_dec(v_fidx_3139_);
    crate::leanh::lean_dec_ref(v_ctx_3138_);
    crate::leanh::lean_dec_ref(v_recArgInfo_3137_);
    return v_res_3148_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0(
    mut v_00_u03b1_3149_: *mut crate::leanh::LeanObject,
    mut v_msg_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
    mut v___y_3152_: *mut crate::leanh::LeanObject,
    mut v___y_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v_msg_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
    return v___x_3156_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___boxed(
    mut v_00_u03b1_3157_: *mut crate::leanh::LeanObject,
    mut v_msg_3158_: *mut crate::leanh::LeanObject,
    mut v___y_3159_: *mut crate::leanh::LeanObject,
    mut v___y_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3164_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0(v_00_u03b1_3157_, v_msg_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
    crate::leanh::lean_dec(v___y_3162_);
    crate::leanh::lean_dec_ref(v___y_3161_);
    crate::leanh::lean_dec(v___y_3160_);
    crate::leanh::lean_dec_ref(v___y_3159_);
    return v_res_3164_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1(
    mut v_00_u03b4_3165_: *mut crate::leanh::LeanObject,
    mut v_t_3166_: *mut crate::leanh::LeanObject,
    mut v_k_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(v_t_3166_, v_k_3167_);
    return v___x_3168_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___boxed(
    mut v_00_u03b4_3169_: *mut crate::leanh::LeanObject,
    mut v_t_3170_: *mut crate::leanh::LeanObject,
    mut v_k_3171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1(v_00_u03b4_3169_, v_t_3170_, v_k_3171_);
    crate::leanh::lean_dec(v_k_3171_);
    crate::leanh::lean_dec(v_t_3170_);
    return v_res_3172_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4(
    mut v_recArgInfo_3173_: *mut crate::leanh::LeanObject,
    mut v_args_3174_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3175_: *mut crate::leanh::LeanObject,
    mut v___x_3176_: *mut crate::leanh::LeanObject,
    mut v_inst_3177_: *mut crate::leanh::LeanObject,
    mut v_R_3178_: *mut crate::leanh::LeanObject,
    mut v_a_3179_: *mut crate::leanh::LeanObject,
    mut v_b_3180_: *mut crate::leanh::LeanObject,
    mut v_c_3181_: *mut crate::leanh::LeanObject,
    mut v___y_3182_: *mut crate::leanh::LeanObject,
    mut v___y_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3187_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(v_recArgInfo_3173_, v_args_3174_, v_upperBound_3175_, v___x_3176_, v_a_3179_, v_b_3180_);
    return v___x_3187_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___boxed(
    mut v_recArgInfo_3188_: *mut crate::leanh::LeanObject,
    mut v_args_3189_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3190_: *mut crate::leanh::LeanObject,
    mut v___x_3191_: *mut crate::leanh::LeanObject,
    mut v_inst_3192_: *mut crate::leanh::LeanObject,
    mut v_R_3193_: *mut crate::leanh::LeanObject,
    mut v_a_3194_: *mut crate::leanh::LeanObject,
    mut v_b_3195_: *mut crate::leanh::LeanObject,
    mut v_c_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
    mut v___y_3198_: *mut crate::leanh::LeanObject,
    mut v___y_3199_: *mut crate::leanh::LeanObject,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4(v_recArgInfo_3188_, v_args_3189_, v_upperBound_3190_, v___x_3191_, v_inst_3192_, v_R_3193_, v_a_3194_, v_b_3195_, v_c_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
    crate::leanh::lean_dec(v___y_3200_);
    crate::leanh::lean_dec_ref(v___y_3199_);
    crate::leanh::lean_dec(v___y_3198_);
    crate::leanh::lean_dec_ref(v___y_3197_);
    crate::leanh::lean_dec(v___x_3191_);
    crate::leanh::lean_dec(v_upperBound_3190_);
    crate::leanh::lean_dec_ref(v_args_3189_);
    crate::leanh::lean_dec_ref(v_recArgInfo_3188_);
    return v_res_3202_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0(
    mut v_k_3203_: *mut crate::leanh::LeanObject,
    mut v___y_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v_b_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
    mut v___y_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3210_);
    crate::leanh::lean_inc_ref(v___y_3209_);
    crate::leanh::lean_inc(v___y_3208_);
    crate::leanh::lean_inc_ref(v___y_3207_);
    crate::leanh::lean_inc(v___y_3205_);
    crate::leanh::lean_inc(v___y_3204_);
    v___x_3212_ = crate::leanh::lean_apply_8(
        v_k_3203_,
        v_b_3206_,
        v___y_3204_,
        v___y_3205_,
        v___y_3207_,
        v___y_3208_,
        v___y_3209_,
        v___y_3210_,
        crate::leanh::lean_box(0),
    );
    return v___x_3212_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0___boxed(
    mut v_k_3213_: *mut crate::leanh::LeanObject,
    mut v___y_3214_: *mut crate::leanh::LeanObject,
    mut v___y_3215_: *mut crate::leanh::LeanObject,
    mut v_b_3216_: *mut crate::leanh::LeanObject,
    mut v___y_3217_: *mut crate::leanh::LeanObject,
    mut v___y_3218_: *mut crate::leanh::LeanObject,
    mut v___y_3219_: *mut crate::leanh::LeanObject,
    mut v___y_3220_: *mut crate::leanh::LeanObject,
    mut v___y_3221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3222_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0(v_k_3213_, v___y_3214_, v___y_3215_, v_b_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
    crate::leanh::lean_dec(v___y_3220_);
    crate::leanh::lean_dec_ref(v___y_3219_);
    crate::leanh::lean_dec(v___y_3218_);
    crate::leanh::lean_dec_ref(v___y_3217_);
    crate::leanh::lean_dec(v___y_3215_);
    crate::leanh::lean_dec(v___y_3214_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(
    mut v_name_3223_: *mut crate::leanh::LeanObject,
    mut v_bi_3224_: u8,
    mut v_type_3225_: *mut crate::leanh::LeanObject,
    mut v_k_3226_: *mut crate::leanh::LeanObject,
    mut v_kind_3227_: u8,
    mut v___y_3228_: *mut crate::leanh::LeanObject,
    mut v___y_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3229_);
                crate::leanh::lean_inc(v___y_3228_);
                v___f_3235_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_3235_, 0, v_k_3226_);
                crate::leanh::lean_closure_set(v___f_3235_, 1, v___y_3228_);
                crate::leanh::lean_closure_set(v___f_3235_, 2, v___y_3229_);
                v___x_3236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3223_,
                    v_bi_3224_,
                    v_type_3225_,
                    v___f_3235_,
                    v_kind_3227_,
                    v___y_3230_,
                    v___y_3231_,
                    v___y_3232_,
                    v___y_3233_,
                );
                if crate::leanh::lean_obj_tag(v___x_3236_) == 0 {
                    return v___x_3236_;
                } else {
                    v_a_3237_ = crate::leanh::lean_ctor_get(v___x_3236_, 0);
                    v_isSharedCheck_3244_ = (!crate::leanh::lean_is_exclusive(v___x_3236_)) as u8;
                    if v_isSharedCheck_3244_ == 0 {
                        v___x_3239_ = v___x_3236_;
                        v_isShared_3240_ = v_isSharedCheck_3244_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3237_);
                        crate::leanh::lean_dec(v___x_3236_);
                        v___x_3239_ = crate::leanh::lean_box(0);
                        v_isShared_3240_ = v_isSharedCheck_3244_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3240_ == 0 {
                    v___x_3242_ = v___x_3239_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
                    v___x_3242_ = v_reuseFailAlloc_3243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___boxed(
    mut v_name_3245_: *mut crate::leanh::LeanObject,
    mut v_bi_3246_: *mut crate::leanh::LeanObject,
    mut v_type_3247_: *mut crate::leanh::LeanObject,
    mut v_k_3248_: *mut crate::leanh::LeanObject,
    mut v_kind_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
    mut v___y_3255_: *mut crate::leanh::LeanObject,
    mut v___y_3256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3257_: u8 = 0;
    let mut v_kind_boxed_3258_: u8 = 0;
    let mut v_res_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3257_ = (crate::leanh::lean_unbox(v_bi_3246_) as u8);
    v_kind_boxed_3258_ = (crate::leanh::lean_unbox(v_kind_3249_) as u8);
    v_res_3259_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_name_3245_, v_bi_boxed_3257_, v_type_3247_, v_k_3248_, v_kind_boxed_3258_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
    crate::leanh::lean_dec(v___y_3255_);
    crate::leanh::lean_dec_ref(v___y_3254_);
    crate::leanh::lean_dec(v___y_3253_);
    crate::leanh::lean_dec_ref(v___y_3252_);
    crate::leanh::lean_dec(v___y_3251_);
    crate::leanh::lean_dec(v___y_3250_);
    return v_res_3259_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3(
    mut v_00_u03b1_3260_: *mut crate::leanh::LeanObject,
    mut v_name_3261_: *mut crate::leanh::LeanObject,
    mut v_bi_3262_: u8,
    mut v_type_3263_: *mut crate::leanh::LeanObject,
    mut v_k_3264_: *mut crate::leanh::LeanObject,
    mut v_kind_3265_: u8,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3273_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_name_3261_, v_bi_3262_, v_type_3263_, v_k_3264_, v_kind_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
    return v___x_3273_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___boxed(
    mut v_00_u03b1_3274_: *mut crate::leanh::LeanObject,
    mut v_name_3275_: *mut crate::leanh::LeanObject,
    mut v_bi_3276_: *mut crate::leanh::LeanObject,
    mut v_type_3277_: *mut crate::leanh::LeanObject,
    mut v_k_3278_: *mut crate::leanh::LeanObject,
    mut v_kind_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v___y_3283_: *mut crate::leanh::LeanObject,
    mut v___y_3284_: *mut crate::leanh::LeanObject,
    mut v___y_3285_: *mut crate::leanh::LeanObject,
    mut v___y_3286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_3287_: u8 = 0;
    let mut v_kind_boxed_3288_: u8 = 0;
    let mut v_res_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_3287_ = (crate::leanh::lean_unbox(v_bi_3276_) as u8);
    v_kind_boxed_3288_ = (crate::leanh::lean_unbox(v_kind_3279_) as u8);
    v_res_3289_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3(v_00_u03b1_3274_, v_name_3275_, v_bi_boxed_3287_, v_type_3277_, v_k_3278_, v_kind_boxed_3288_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
    crate::leanh::lean_dec(v___y_3285_);
    crate::leanh::lean_dec_ref(v___y_3284_);
    crate::leanh::lean_dec(v___y_3283_);
    crate::leanh::lean_dec_ref(v___y_3282_);
    crate::leanh::lean_dec(v___y_3281_);
    crate::leanh::lean_dec(v___y_3280_);
    return v_res_3289_;
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0(
    mut v_k_3290_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_3291_: u8,
    mut v_x_3292_: *mut crate::leanh::LeanObject,
    mut v___y_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
    mut v___y_3295_: *mut crate::leanh::LeanObject,
    mut v___y_3296_: *mut crate::leanh::LeanObject,
    mut v___y_3297_: *mut crate::leanh::LeanObject,
    mut v___y_3298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3298_);
    crate::leanh::lean_inc_ref(v___y_3297_);
    crate::leanh::lean_inc(v___y_3296_);
    crate::leanh::lean_inc_ref(v___y_3295_);
    crate::leanh::lean_inc(v___y_3294_);
    crate::leanh::lean_inc(v___y_3293_);
    crate::leanh::lean_inc_ref(v_x_3292_);
    v___x_3300_ = crate::leanh::lean_apply_8(
        v_k_3290_,
        v_x_3292_,
        v___y_3293_,
        v___y_3294_,
        v___y_3295_,
        v___y_3296_,
        v___y_3297_,
        v___y_3298_,
        crate::leanh::lean_box(0),
    );
    if crate::leanh::lean_obj_tag(v___x_3300_) == 0 {
        let mut v_a_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: u8 = 0;
        let mut v___x_3306_: u8 = 0;
        let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3301_ = crate::leanh::lean_ctor_get(v___x_3300_, 0);
        crate::leanh::lean_inc(v_a_3301_);
        crate::leanh::lean_dec_ref_known(v___x_3300_, 1);
        v___x_3302_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3303_ = lean_mk_empty_array_with_capacity(v___x_3302_);
        v___x_3304_ = lean_array_push(v___x_3303_, v_x_3292_);
        v___x_3305_ = 0;
        v___x_3306_ = 1;
        v___x_3307_ = l_Lean_Meta_mkLetFVars(
            v___x_3304_,
            v_a_3301_,
            v_usedLetOnly_3291_,
            v___x_3305_,
            v___x_3306_,
            v___y_3295_,
            v___y_3296_,
            v___y_3297_,
            v___y_3298_,
        );
        crate::leanh::lean_dec_ref(v___x_3304_);
        return v___x_3307_;
    } else {
        crate::leanh::lean_dec_ref(v_x_3292_);
        return v___x_3300_;
    }
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0___boxed(
    mut v_k_3308_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_3309_: *mut crate::leanh::LeanObject,
    mut v_x_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
    mut v___y_3312_: *mut crate::leanh::LeanObject,
    mut v___y_3313_: *mut crate::leanh::LeanObject,
    mut v___y_3314_: *mut crate::leanh::LeanObject,
    mut v___y_3315_: *mut crate::leanh::LeanObject,
    mut v___y_3316_: *mut crate::leanh::LeanObject,
    mut v___y_3317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_usedLetOnly_boxed_3318_: u8 = 0;
    let mut v_res_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_3318_ = (crate::leanh::lean_unbox(v_usedLetOnly_3309_) as u8);
    v_res_3319_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0(v_k_3308_, v_usedLetOnly_boxed_3318_, v_x_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
    crate::leanh::lean_dec(v___y_3316_);
    crate::leanh::lean_dec_ref(v___y_3315_);
    crate::leanh::lean_dec(v___y_3314_);
    crate::leanh::lean_dec_ref(v___y_3313_);
    crate::leanh::lean_dec(v___y_3312_);
    crate::leanh::lean_dec(v___y_3311_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(
    mut v_name_3320_: *mut crate::leanh::LeanObject,
    mut v_type_3321_: *mut crate::leanh::LeanObject,
    mut v_val_3322_: *mut crate::leanh::LeanObject,
    mut v_k_3323_: *mut crate::leanh::LeanObject,
    mut v_nondep_3324_: u8,
    mut v_kind_3325_: u8,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
    mut v___y_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_3327_);
                crate::leanh::lean_inc(v___y_3326_);
                v___f_3333_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                crate::leanh::lean_closure_set(v___f_3333_, 0, v_k_3323_);
                crate::leanh::lean_closure_set(v___f_3333_, 1, v___y_3326_);
                crate::leanh::lean_closure_set(v___f_3333_, 2, v___y_3327_);
                v___x_3334_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_3320_,
                    v_type_3321_,
                    v_val_3322_,
                    v___f_3333_,
                    v_nondep_3324_,
                    v_kind_3325_,
                    v___y_3328_,
                    v___y_3329_,
                    v___y_3330_,
                    v___y_3331_,
                );
                if crate::leanh::lean_obj_tag(v___x_3334_) == 0 {
                    return v___x_3334_;
                } else {
                    v_a_3335_ = crate::leanh::lean_ctor_get(v___x_3334_, 0);
                    v_isSharedCheck_3342_ = (!crate::leanh::lean_is_exclusive(v___x_3334_)) as u8;
                    if v_isSharedCheck_3342_ == 0 {
                        v___x_3337_ = v___x_3334_;
                        v_isShared_3338_ = v_isSharedCheck_3342_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3335_);
                        crate::leanh::lean_dec(v___x_3334_);
                        v___x_3337_ = crate::leanh::lean_box(0);
                        v_isShared_3338_ = v_isSharedCheck_3342_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3338_ == 0 {
                    v___x_3340_ = v___x_3337_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
                    v___x_3340_ = v_reuseFailAlloc_3341_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3340_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg___boxed(
    mut v_name_3343_: *mut crate::leanh::LeanObject,
    mut v_type_3344_: *mut crate::leanh::LeanObject,
    mut v_val_3345_: *mut crate::leanh::LeanObject,
    mut v_k_3346_: *mut crate::leanh::LeanObject,
    mut v_nondep_3347_: *mut crate::leanh::LeanObject,
    mut v_kind_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
    mut v___y_3350_: *mut crate::leanh::LeanObject,
    mut v___y_3351_: *mut crate::leanh::LeanObject,
    mut v___y_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_3356_: u8 = 0;
    let mut v_kind_boxed_3357_: u8 = 0;
    let mut v_res_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3356_ = (crate::leanh::lean_unbox(v_nondep_3347_) as u8);
    v_kind_boxed_3357_ = (crate::leanh::lean_unbox(v_kind_3348_) as u8);
    v_res_3358_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(v_name_3343_, v_type_3344_, v_val_3345_, v_k_3346_, v_nondep_boxed_3356_, v_kind_boxed_3357_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
    crate::leanh::lean_dec(v___y_3354_);
    crate::leanh::lean_dec_ref(v___y_3353_);
    crate::leanh::lean_dec(v___y_3352_);
    crate::leanh::lean_dec_ref(v___y_3351_);
    crate::leanh::lean_dec(v___y_3350_);
    crate::leanh::lean_dec(v___y_3349_);
    return v_res_3358_;
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4(
    mut v_name_3359_: *mut crate::leanh::LeanObject,
    mut v_type_3360_: *mut crate::leanh::LeanObject,
    mut v_val_3361_: *mut crate::leanh::LeanObject,
    mut v_k_3362_: *mut crate::leanh::LeanObject,
    mut v_nondep_3363_: u8,
    mut v_kind_3364_: u8,
    mut v_usedLetOnly_3365_: u8,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
    mut v___y_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3373_ = crate::leanh::lean_box((v_usedLetOnly_3365_) as usize);
    v___f_3374_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
    crate::leanh::lean_closure_set(v___f_3374_, 0, v_k_3362_);
    crate::leanh::lean_closure_set(v___f_3374_, 1, v___x_3373_);
    v___x_3375_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(v_name_3359_, v_type_3360_, v_val_3361_, v___f_3374_, v_nondep_3363_, v_kind_3364_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    return v___x_3375_;
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___boxed(
    mut v_name_3376_: *mut crate::leanh::LeanObject,
    mut v_type_3377_: *mut crate::leanh::LeanObject,
    mut v_val_3378_: *mut crate::leanh::LeanObject,
    mut v_k_3379_: *mut crate::leanh::LeanObject,
    mut v_nondep_3380_: *mut crate::leanh::LeanObject,
    mut v_kind_3381_: *mut crate::leanh::LeanObject,
    mut v_usedLetOnly_3382_: *mut crate::leanh::LeanObject,
    mut v___y_3383_: *mut crate::leanh::LeanObject,
    mut v___y_3384_: *mut crate::leanh::LeanObject,
    mut v___y_3385_: *mut crate::leanh::LeanObject,
    mut v___y_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_3390_: u8 = 0;
    let mut v_kind_boxed_3391_: u8 = 0;
    let mut v_usedLetOnly_boxed_3392_: u8 = 0;
    let mut v_res_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3390_ = (crate::leanh::lean_unbox(v_nondep_3380_) as u8);
    v_kind_boxed_3391_ = (crate::leanh::lean_unbox(v_kind_3381_) as u8);
    v_usedLetOnly_boxed_3392_ = (crate::leanh::lean_unbox(v_usedLetOnly_3382_) as u8);
    v_res_3393_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4(v_name_3376_, v_type_3377_, v_val_3378_, v_k_3379_, v_nondep_boxed_3390_, v_kind_boxed_3391_, v_usedLetOnly_boxed_3392_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
    crate::leanh::lean_dec(v___y_3388_);
    crate::leanh::lean_dec_ref(v___y_3387_);
    crate::leanh::lean_dec(v___y_3386_);
    crate::leanh::lean_dec_ref(v___y_3385_);
    crate::leanh::lean_dec(v___y_3384_);
    crate::leanh::lean_dec(v___y_3383_);
    return v_res_3393_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3(
    mut v_xs_3394_: *mut crate::leanh::LeanObject,
    mut v_v_3395_: *mut crate::leanh::LeanObject,
    mut v_i_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3397_ = lean_array_get_size(v_xs_3394_);
                v___x_3398_ = lean_nat_dec_lt(v_i_3396_, v___x_3397_);
                if v___x_3398_ == 0 {
                    crate::leanh::lean_dec(v_i_3396_);
                    v___x_3399_ = crate::leanh::lean_box(0);
                    return v___x_3399_;
                } else {
                    v___x_3400_ = lean_array_fget_borrowed(v_xs_3394_, v_i_3396_);
                    v___x_3401_ = lean_name_eq(v___x_3400_, v_v_3395_);
                    if v___x_3401_ == 0 {
                        v___x_3402_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3403_ = lean_nat_add(v_i_3396_, v___x_3402_);
                        crate::leanh::lean_dec(v_i_3396_);
                        v_i_3396_ = v___x_3403_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3405_, 0, v_i_3396_);
                        return v___x_3405_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3___boxed(
    mut v_xs_3406_: *mut crate::leanh::LeanObject,
    mut v_v_3407_: *mut crate::leanh::LeanObject,
    mut v_i_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3409_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3(v_xs_3406_, v_v_3407_, v_i_3408_);
    crate::leanh::lean_dec(v_v_3407_);
    crate::leanh::lean_dec_ref(v_xs_3406_);
    return v_res_3409_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1(
    mut v_xs_3410_: *mut crate::leanh::LeanObject,
    mut v_v_3411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3412_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3413_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3(v_xs_3410_, v_v_3411_, v___x_3412_);
    return v___x_3413_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1___boxed(
    mut v_xs_3414_: *mut crate::leanh::LeanObject,
    mut v_v_3415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1(v_xs_3414_, v_v_3415_);
    crate::leanh::lean_dec(v_v_3415_);
    crate::leanh::lean_dec_ref(v_xs_3414_);
    return v_res_3416_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1(
    mut v_xs_3417_: *mut crate::leanh::LeanObject,
    mut v_v_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3419_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1(v_xs_3417_, v_v_3418_);
                if crate::leanh::lean_obj_tag(v___x_3419_) == 0 {
                    v___x_3420_ = crate::leanh::lean_box(0);
                    return v___x_3420_;
                } else {
                    v_val_3421_ = crate::leanh::lean_ctor_get(v___x_3419_, 0);
                    v_isSharedCheck_3428_ = (!crate::leanh::lean_is_exclusive(v___x_3419_)) as u8;
                    if v_isSharedCheck_3428_ == 0 {
                        v___x_3423_ = v___x_3419_;
                        v_isShared_3424_ = v_isSharedCheck_3428_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3421_);
                        crate::leanh::lean_dec(v___x_3419_);
                        v___x_3423_ = crate::leanh::lean_box(0);
                        v_isShared_3424_ = v_isSharedCheck_3428_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3424_ == 0 {
                    v___x_3426_ = v___x_3423_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_val_3421_);
                    v___x_3426_ = v_reuseFailAlloc_3427_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1___boxed(
    mut v_xs_3429_: *mut crate::leanh::LeanObject,
    mut v_v_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3431_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1(v_xs_3429_, v_v_3430_);
    crate::leanh::lean_dec(v_v_3430_);
    crate::leanh::lean_dec_ref(v_xs_3429_);
    return v_res_3431_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0()
-> f64 {
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: f64 = 0.0;
    v___x_3432_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3433_ = lean_float_of_nat(v___x_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(
    mut v_cls_3437_: *mut crate::leanh::LeanObject,
    mut v_msg_3438_: *mut crate::leanh::LeanObject,
    mut v___y_3439_: *mut crate::leanh::LeanObject,
    mut v___y_3440_: *mut crate::leanh::LeanObject,
    mut v___y_3441_: *mut crate::leanh::LeanObject,
    mut v___y_3442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_tid_3463_: u64 = 0;
    let mut v_traces_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: f64 = 0.0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3444_ = crate::leanh::lean_ctor_get(v___y_3441_, 5);
                v___x_3445_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msg_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
                v_a_3446_ = crate::leanh::lean_ctor_get(v___x_3445_, 0);
                v_isSharedCheck_3490_ = (!crate::leanh::lean_is_exclusive(v___x_3445_)) as u8;
                if v_isSharedCheck_3490_ == 0 {
                    v___x_3448_ = v___x_3445_;
                    v_isShared_3449_ = v_isSharedCheck_3490_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3446_);
                    crate::leanh::lean_dec(v___x_3445_);
                    v___x_3448_ = crate::leanh::lean_box(0);
                    v_isShared_3449_ = v_isSharedCheck_3490_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3450_ = lean_st_ref_take(v___y_3442_);
                v_traceState_3451_ = crate::leanh::lean_ctor_get(v___x_3450_, 4);
                v_env_3452_ = crate::leanh::lean_ctor_get(v___x_3450_, 0);
                v_nextMacroScope_3453_ = crate::leanh::lean_ctor_get(v___x_3450_, 1);
                v_ngen_3454_ = crate::leanh::lean_ctor_get(v___x_3450_, 2);
                v_auxDeclNGen_3455_ = crate::leanh::lean_ctor_get(v___x_3450_, 3);
                v_cache_3456_ = crate::leanh::lean_ctor_get(v___x_3450_, 5);
                v_messages_3457_ = crate::leanh::lean_ctor_get(v___x_3450_, 6);
                v_infoState_3458_ = crate::leanh::lean_ctor_get(v___x_3450_, 7);
                v_snapshotTasks_3459_ = crate::leanh::lean_ctor_get(v___x_3450_, 8);
                v_isSharedCheck_3489_ = (!crate::leanh::lean_is_exclusive(v___x_3450_)) as u8;
                if v_isSharedCheck_3489_ == 0 {
                    v___x_3461_ = v___x_3450_;
                    v_isShared_3462_ = v_isSharedCheck_3489_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3459_);
                    crate::leanh::lean_inc(v_infoState_3458_);
                    crate::leanh::lean_inc(v_messages_3457_);
                    crate::leanh::lean_inc(v_cache_3456_);
                    crate::leanh::lean_inc(v_traceState_3451_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3455_);
                    crate::leanh::lean_inc(v_ngen_3454_);
                    crate::leanh::lean_inc(v_nextMacroScope_3453_);
                    crate::leanh::lean_inc(v_env_3452_);
                    crate::leanh::lean_dec(v___x_3450_);
                    v___x_3461_ = crate::leanh::lean_box(0);
                    v_isShared_3462_ = v_isSharedCheck_3489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3463_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3451_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3464_ = crate::leanh::lean_ctor_get(v_traceState_3451_, 0);
                v_isSharedCheck_3488_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3451_)) as u8;
                if v_isSharedCheck_3488_ == 0 {
                    v___x_3466_ = v_traceState_3451_;
                    v_isShared_3467_ = v_isSharedCheck_3488_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3464_);
                    crate::leanh::lean_dec(v_traceState_3451_);
                    v___x_3466_ = crate::leanh::lean_box(0);
                    v_isShared_3467_ = v_isSharedCheck_3488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3468_ = crate::leanh::lean_box(0);
                v___x_3469_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0);
                v___x_3470_ = 0;
                v___x_3471_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1;
                v___x_3472_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3472_, 0, v_cls_3437_);
                crate::leanh::lean_ctor_set(v___x_3472_, 1, v___x_3468_);
                crate::leanh::lean_ctor_set(v___x_3472_, 2, v___x_3471_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3472_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3469_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3472_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3469_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3472_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3470_,
                );
                v___x_3473_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2;
                v___x_3474_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3474_, 0, v___x_3472_);
                crate::leanh::lean_ctor_set(v___x_3474_, 1, v_a_3446_);
                crate::leanh::lean_ctor_set(v___x_3474_, 2, v___x_3473_);
                crate::leanh::lean_inc(v_ref_3444_);
                v___x_3475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3475_, 0, v_ref_3444_);
                crate::leanh::lean_ctor_set(v___x_3475_, 1, v___x_3474_);
                v___x_3476_ = l_Lean_PersistentArray_push___redArg(v_traces_3464_, v___x_3475_);
                if v_isShared_3467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3466_, 0, v___x_3476_);
                    v___x_3478_ = v___x_3466_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3476_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3487_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3463_,
                    );
                    v___x_3478_ = v_reuseFailAlloc_3487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3461_, 4, v___x_3478_);
                    v___x_3480_ = v___x_3461_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3486_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_env_3452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_nextMacroScope_3453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_ngen_3454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_auxDeclNGen_3455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 4, v___x_3478_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 5, v_cache_3456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 6, v_messages_3457_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 7, v_infoState_3458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 8, v_snapshotTasks_3459_);
                    v___x_3480_ = v_reuseFailAlloc_3486_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3481_ = lean_st_ref_set(v___y_3442_, v___x_3480_);
                v___x_3482_ = crate::leanh::lean_box(0);
                if v_isShared_3449_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3448_, 0, v___x_3482_);
                    v___x_3484_ = v___x_3448_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
                    v___x_3484_ = v_reuseFailAlloc_3485_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___boxed(
    mut v_cls_3491_: *mut crate::leanh::LeanObject,
    mut v_msg_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(v_cls_3491_, v_msg_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
    crate::leanh::lean_dec(v___y_3496_);
    crate::leanh::lean_dec_ref(v___y_3495_);
    crate::leanh::lean_dec(v___y_3494_);
    crate::leanh::lean_dec_ref(v___y_3493_);
    return v_res_3498_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__6(
    mut v_e_3499_: *mut crate::leanh::LeanObject,
    mut v_as_3500_: *mut crate::leanh::LeanObject,
    mut v_i_3501_: usize,
    mut v_stop_3502_: usize,
) -> u8 {
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnName_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: usize = 0;
    let mut v___x_3509_: usize = 0;
    let mut v___x_3511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3503_ = lean_usize_dec_eq(v_i_3501_, v_stop_3502_);
                if v___x_3503_ == 0 {
                    v___x_3504_ = lean_array_uget_borrowed(v_as_3500_, v_i_3501_);
                    v_fnName_3505_ = crate::leanh::lean_ctor_get(v___x_3504_, 0);
                    v_recArgPos_3506_ = crate::leanh::lean_ctor_get(v___x_3504_, 2);
                    crate::leanh::lean_inc(v_recArgPos_3506_);
                    crate::leanh::lean_inc(v_fnName_3505_);
                    v___x_3507_ = l_Lean_Elab_Structural_recArgHasLooseBVarsAt(
                        v_fnName_3505_,
                        v_recArgPos_3506_,
                        v_e_3499_,
                    );
                    if v___x_3507_ == 0 {
                        v___x_3508_ = 1usize;
                        v___x_3509_ = lean_usize_add(v_i_3501_, v___x_3508_);
                        v_i_3501_ = v___x_3509_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3507_;
                    }
                } else {
                    v___x_3511_ = 0;
                    return v___x_3511_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__6___boxed(
    mut v_e_3512_: *mut crate::leanh::LeanObject,
    mut v_as_3513_: *mut crate::leanh::LeanObject,
    mut v_i_3514_: *mut crate::leanh::LeanObject,
    mut v_stop_3515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3516_: usize = 0;
    let mut v_stop_boxed_3517_: usize = 0;
    let mut v_res_3518_: u8 = 0;
    let mut v_r_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3516_ = crate::leanh::lean_unbox_usize(v_i_3514_);
    crate::leanh::lean_dec(v_i_3514_);
    v_stop_boxed_3517_ = crate::leanh::lean_unbox_usize(v_stop_3515_);
    crate::leanh::lean_dec(v_stop_3515_);
    v_res_3518_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__6(v_e_3512_, v_as_3513_, v_i_boxed_3516_, v_stop_boxed_3517_);
    crate::leanh::lean_dec_ref(v_as_3513_);
    crate::leanh::lean_dec_ref(v_e_3512_);
    v_r_3519_ = crate::leanh::lean_box((v_res_3518_) as usize);
    return v_r_3519_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3520_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3521_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0);
    v___x_3522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3522_, 0, v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3523_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_3524_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3525_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3525_, 0, v___x_3524_);
    crate::leanh::lean_ctor_set(v___x_3525_, 1, v___x_3524_);
    crate::leanh::lean_ctor_set(v___x_3525_, 2, v___x_3524_);
    crate::leanh::lean_ctor_set(v___x_3525_, 3, v___x_3524_);
    crate::leanh::lean_ctor_set(v___x_3525_, 4, v___x_3523_);
    crate::leanh::lean_ctor_set(v___x_3525_, 5, v___x_3523_);
    crate::leanh::lean_ctor_set(v___x_3525_, 6, v___x_3523_);
    crate::leanh::lean_ctor_set(v___x_3525_, 7, v___x_3523_);
    crate::leanh::lean_ctor_set(v___x_3525_, 8, v___x_3523_);
    crate::leanh::lean_ctor_set(v___x_3525_, 9, v___x_3523_);
    return v___x_3525_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3527_ = lean_mk_empty_array_with_capacity(v___x_3526_);
    v___x_3528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3528_, 0, v___x_3527_);
    return v___x_3528_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3529_: usize = 0;
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3529_ = 5usize;
    v___x_3530_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3531_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3532_ = lean_mk_empty_array_with_capacity(v___x_3531_);
    v___x_3533_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
    v___x_3534_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3534_, 0, v___x_3533_);
    crate::leanh::lean_ctor_set(v___x_3534_, 1, v___x_3532_);
    crate::leanh::lean_ctor_set(v___x_3534_, 2, v___x_3530_);
    crate::leanh::lean_ctor_set(v___x_3534_, 3, v___x_3530_);
    crate::leanh::lean_ctor_set_usize(v___x_3534_, 4, v___x_3529_);
    return v___x_3534_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3535_ = crate::leanh::lean_box(1);
    v___x_3536_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4);
    v___x_3537_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_3538_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3538_, 0, v___x_3537_);
    crate::leanh::lean_ctor_set(v___x_3538_, 1, v___x_3536_);
    crate::leanh::lean_ctor_set(v___x_3538_, 2, v___x_3535_);
    return v___x_3538_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_3541_ = l_Lean_stringToMessageData(v___x_3540_);
    return v___x_3541_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3543_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_3544_ = l_Lean_stringToMessageData(v___x_3543_);
    return v___x_3544_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_3547_ = l_Lean_stringToMessageData(v___x_3546_);
    return v___x_3547_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3549_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_3550_ = l_Lean_stringToMessageData(v___x_3549_);
    return v___x_3550_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3552_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14;
    v___x_3553_ = l_Lean_stringToMessageData(v___x_3552_);
    return v___x_3553_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16;
    v___x_3556_ = l_Lean_stringToMessageData(v___x_3555_);
    return v___x_3556_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18;
    v___x_3559_ = l_Lean_stringToMessageData(v___x_3558_);
    return v___x_3559_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(
    mut v_msg_3560_: *mut crate::leanh::LeanObject,
    mut v_declHint_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: u8 = 0;
    let mut v_isExporting_3567_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3589_: u8 = 0;
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3621_: u8 = 0;
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3564_ = lean_st_ref_get(v___y_3562_);
                v_env_3565_ = crate::leanh::lean_ctor_get(v___x_3564_, 0);
                crate::leanh::lean_inc_ref(v_env_3565_);
                crate::leanh::lean_dec(v___x_3564_);
                v___x_3566_ = l_Lean_Name_isAnonymous(v_declHint_3561_);
                if v___x_3566_ == 0 {
                    v_isExporting_3567_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_3565_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3567_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_3565_);
                        crate::leanh::lean_dec(v_declHint_3561_);
                        v___x_3568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3568_, 0, v_msg_3560_);
                        return v___x_3568_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_3565_);
                        v___x_3569_ = l_Lean_Environment_setExporting(v_env_3565_, v___x_3566_);
                        crate::leanh::lean_inc(v_declHint_3561_);
                        crate::leanh::lean_inc_ref(v___x_3569_);
                        v___x_3570_ = l_Lean_Environment_contains(
                            v___x_3569_,
                            v_declHint_3561_,
                            v_isExporting_3567_,
                        );
                        if v___x_3570_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_3569_);
                            crate::leanh::lean_dec_ref(v_env_3565_);
                            crate::leanh::lean_dec(v_declHint_3561_);
                            v___x_3571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3571_, 0, v_msg_3560_);
                            return v___x_3571_;
                        } else {
                            v___x_3572_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2);
                            v___x_3573_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
                            v___x_3574_ = l_Lean_Options_empty;
                            v___x_3575_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3575_, 0, v___x_3569_);
                            crate::leanh::lean_ctor_set(v___x_3575_, 1, v___x_3572_);
                            crate::leanh::lean_ctor_set(v___x_3575_, 2, v___x_3573_);
                            crate::leanh::lean_ctor_set(v___x_3575_, 3, v___x_3574_);
                            crate::leanh::lean_inc(v_declHint_3561_);
                            v___x_3576_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3561_, v___x_3566_);
                            v_c_3577_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_3577_, 0, v___x_3575_);
                            crate::leanh::lean_ctor_set(v_c_3577_, 1, v___x_3576_);
                            v___x_3578_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3565_,
                                v_declHint_3561_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3578_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_3565_);
                                crate::leanh::lean_dec(v_declHint_3561_);
                                v___x_3579_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
                                v___x_3580_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3580_, 0, v___x_3579_);
                                crate::leanh::lean_ctor_set(v___x_3580_, 1, v_c_3577_);
                                v___x_3581_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
                                v___x_3582_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3582_, 0, v___x_3580_);
                                crate::leanh::lean_ctor_set(v___x_3582_, 1, v___x_3581_);
                                v___x_3583_ = l_Lean_MessageData_note(v___x_3582_);
                                v___x_3584_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3584_, 0, v_msg_3560_);
                                crate::leanh::lean_ctor_set(v___x_3584_, 1, v___x_3583_);
                                v___x_3585_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3585_, 0, v___x_3584_);
                                return v___x_3585_;
                            } else {
                                v_val_3586_ = crate::leanh::lean_ctor_get(v___x_3578_, 0);
                                v_isSharedCheck_3621_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3578_)) as u8;
                                if v_isSharedCheck_3621_ == 0 {
                                    v___x_3588_ = v___x_3578_;
                                    v_isShared_3589_ = v_isSharedCheck_3621_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_3586_);
                                    crate::leanh::lean_dec(v___x_3578_);
                                    v___x_3588_ = crate::leanh::lean_box(0);
                                    v_isShared_3589_ = v_isSharedCheck_3621_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_3565_);
                    crate::leanh::lean_dec(v_declHint_3561_);
                    v___x_3622_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3622_, 0, v_msg_3560_);
                    return v___x_3622_;
                }
            }
            1 => {
                v___x_3590_ = crate::leanh::lean_box(0);
                v___x_3591_ = l_Lean_Environment_header(v_env_3565_);
                crate::leanh::lean_dec_ref(v_env_3565_);
                v___x_3592_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3591_);
                v_mod_3593_ = lean_array_get(v___x_3590_, v___x_3592_, v_val_3586_);
                crate::leanh::lean_dec(v_val_3586_);
                crate::leanh::lean_dec_ref(v___x_3592_);
                v___x_3594_ = l_Lean_isPrivateName(v_declHint_3561_);
                crate::leanh::lean_dec(v_declHint_3561_);
                if v___x_3594_ == 0 {
                    v___x_3595_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_3596_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3596_, 0, v___x_3595_);
                    crate::leanh::lean_ctor_set(v___x_3596_, 1, v_c_3577_);
                    v___x_3597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_3598_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3598_, 0, v___x_3596_);
                    crate::leanh::lean_ctor_set(v___x_3598_, 1, v___x_3597_);
                    v___x_3599_ = l_Lean_MessageData_ofName(v_mod_3593_);
                    v___x_3600_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3600_, 0, v___x_3598_);
                    crate::leanh::lean_ctor_set(v___x_3600_, 1, v___x_3599_);
                    v___x_3601_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15);
                    v___x_3602_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3602_, 0, v___x_3600_);
                    crate::leanh::lean_ctor_set(v___x_3602_, 1, v___x_3601_);
                    v___x_3603_ = l_Lean_MessageData_note(v___x_3602_);
                    v___x_3604_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3604_, 0, v_msg_3560_);
                    crate::leanh::lean_ctor_set(v___x_3604_, 1, v___x_3603_);
                    if v_isShared_3589_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3588_, 0);
                        crate::leanh::lean_ctor_set(v___x_3588_, 0, v___x_3604_);
                        v___x_3606_ = v___x_3588_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3607_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
                        v___x_3606_ = v_reuseFailAlloc_3607_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3608_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_3609_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3609_, 0, v___x_3608_);
                    crate::leanh::lean_ctor_set(v___x_3609_, 1, v_c_3577_);
                    v___x_3610_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17);
                    v___x_3611_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3611_, 0, v___x_3609_);
                    crate::leanh::lean_ctor_set(v___x_3611_, 1, v___x_3610_);
                    v___x_3612_ = l_Lean_MessageData_ofName(v_mod_3593_);
                    v___x_3613_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                    crate::leanh::lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                    v___x_3614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19);
                    v___x_3615_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                    crate::leanh::lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                    v___x_3616_ = l_Lean_MessageData_note(v___x_3615_);
                    v___x_3617_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3617_, 0, v_msg_3560_);
                    crate::leanh::lean_ctor_set(v___x_3617_, 1, v___x_3616_);
                    if v_isShared_3589_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3588_, 0);
                        crate::leanh::lean_ctor_set(v___x_3588_, 0, v___x_3617_);
                        v___x_3619_ = v___x_3588_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3620_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
                        v___x_3619_ = v_reuseFailAlloc_3620_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3606_;
            }
            3 => {
                return v___x_3619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___boxed(
    mut v_msg_3623_: *mut crate::leanh::LeanObject,
    mut v_declHint_3624_: *mut crate::leanh::LeanObject,
    mut v___y_3625_: *mut crate::leanh::LeanObject,
    mut v___y_3626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3623_, v_declHint_3624_, v___y_3625_);
    crate::leanh::lean_dec(v___y_3625_);
    return v_res_3627_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17(
    mut v_msg_3628_: *mut crate::leanh::LeanObject,
    mut v_declHint_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3628_, v_declHint_3629_, v___y_3635_);
                v_a_3638_ = crate::leanh::lean_ctor_get(v___x_3637_, 0);
                v_isSharedCheck_3647_ = (!crate::leanh::lean_is_exclusive(v___x_3637_)) as u8;
                if v_isSharedCheck_3647_ == 0 {
                    v___x_3640_ = v___x_3637_;
                    v_isShared_3641_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3638_);
                    crate::leanh::lean_dec(v___x_3637_);
                    v___x_3640_ = crate::leanh::lean_box(0);
                    v_isShared_3641_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3642_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3643_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3643_, 0, v___x_3642_);
                crate::leanh::lean_ctor_set(v___x_3643_, 1, v_a_3638_);
                if v_isShared_3641_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3640_, 0, v___x_3643_);
                    v___x_3645_ = v___x_3640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3643_);
                    v___x_3645_ = v_reuseFailAlloc_3646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3645_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17___boxed(
    mut v_msg_3648_: *mut crate::leanh::LeanObject,
    mut v_declHint_3649_: *mut crate::leanh::LeanObject,
    mut v___y_3650_: *mut crate::leanh::LeanObject,
    mut v___y_3651_: *mut crate::leanh::LeanObject,
    mut v___y_3652_: *mut crate::leanh::LeanObject,
    mut v___y_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17(v_msg_3648_, v_declHint_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
    crate::leanh::lean_dec(v___y_3655_);
    crate::leanh::lean_dec_ref(v___y_3654_);
    crate::leanh::lean_dec(v___y_3653_);
    crate::leanh::lean_dec_ref(v___y_3652_);
    crate::leanh::lean_dec(v___y_3651_);
    crate::leanh::lean_dec(v___y_3650_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(
    mut v_msg_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
    mut v___y_3660_: *mut crate::leanh::LeanObject,
    mut v___y_3661_: *mut crate::leanh::LeanObject,
    mut v___y_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3669_: u8 = 0;
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3664_ = crate::leanh::lean_ctor_get(v___y_3661_, 5);
                v___x_3665_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msg_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
                v_a_3666_ = crate::leanh::lean_ctor_get(v___x_3665_, 0);
                v_isSharedCheck_3674_ = (!crate::leanh::lean_is_exclusive(v___x_3665_)) as u8;
                if v_isSharedCheck_3674_ == 0 {
                    v___x_3668_ = v___x_3665_;
                    v_isShared_3669_ = v_isSharedCheck_3674_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3666_);
                    crate::leanh::lean_dec(v___x_3665_);
                    v___x_3668_ = crate::leanh::lean_box(0);
                    v_isShared_3669_ = v_isSharedCheck_3674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3664_);
                v___x_3670_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3670_, 0, v_ref_3664_);
                crate::leanh::lean_ctor_set(v___x_3670_, 1, v_a_3666_);
                if v_isShared_3669_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3668_, 1);
                    crate::leanh::lean_ctor_set(v___x_3668_, 0, v___x_3670_);
                    v___x_3672_ = v___x_3668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
                    v___x_3672_ = v_reuseFailAlloc_3673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg___boxed(
    mut v_msg_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(v_msg_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
    crate::leanh::lean_dec(v___y_3679_);
    crate::leanh::lean_dec_ref(v___y_3678_);
    crate::leanh::lean_dec(v___y_3677_);
    crate::leanh::lean_dec_ref(v___y_3676_);
    return v_res_3681_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(
    mut v_ref_3682_: *mut crate::leanh::LeanObject,
    mut v_msg_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3703_: u8 = 0;
    let mut v_cancelTk_x3f_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3705_: u8 = 0;
    let mut v_inheritedTraceOptions_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3691_ = crate::leanh::lean_ctor_get(v___y_3688_, 0);
    v_fileMap_3692_ = crate::leanh::lean_ctor_get(v___y_3688_, 1);
    v_options_3693_ = crate::leanh::lean_ctor_get(v___y_3688_, 2);
    v_currRecDepth_3694_ = crate::leanh::lean_ctor_get(v___y_3688_, 3);
    v_maxRecDepth_3695_ = crate::leanh::lean_ctor_get(v___y_3688_, 4);
    v_ref_3696_ = crate::leanh::lean_ctor_get(v___y_3688_, 5);
    v_currNamespace_3697_ = crate::leanh::lean_ctor_get(v___y_3688_, 6);
    v_openDecls_3698_ = crate::leanh::lean_ctor_get(v___y_3688_, 7);
    v_initHeartbeats_3699_ = crate::leanh::lean_ctor_get(v___y_3688_, 8);
    v_maxHeartbeats_3700_ = crate::leanh::lean_ctor_get(v___y_3688_, 9);
    v_quotContext_3701_ = crate::leanh::lean_ctor_get(v___y_3688_, 10);
    v_currMacroScope_3702_ = crate::leanh::lean_ctor_get(v___y_3688_, 11);
    v_diag_3703_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3688_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3704_ = crate::leanh::lean_ctor_get(v___y_3688_, 12);
    v_suppressElabErrors_3705_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3688_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3706_ = crate::leanh::lean_ctor_get(v___y_3688_, 13);
    v_ref_3707_ = l_Lean_replaceRef(v_ref_3682_, v_ref_3696_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3706_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3704_);
    crate::leanh::lean_inc(v_currMacroScope_3702_);
    crate::leanh::lean_inc(v_quotContext_3701_);
    crate::leanh::lean_inc(v_maxHeartbeats_3700_);
    crate::leanh::lean_inc(v_initHeartbeats_3699_);
    crate::leanh::lean_inc(v_openDecls_3698_);
    crate::leanh::lean_inc(v_currNamespace_3697_);
    crate::leanh::lean_inc(v_maxRecDepth_3695_);
    crate::leanh::lean_inc(v_currRecDepth_3694_);
    crate::leanh::lean_inc_ref(v_options_3693_);
    crate::leanh::lean_inc_ref(v_fileMap_3692_);
    crate::leanh::lean_inc_ref(v_fileName_3691_);
    v___x_3708_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3708_, 0, v_fileName_3691_);
    crate::leanh::lean_ctor_set(v___x_3708_, 1, v_fileMap_3692_);
    crate::leanh::lean_ctor_set(v___x_3708_, 2, v_options_3693_);
    crate::leanh::lean_ctor_set(v___x_3708_, 3, v_currRecDepth_3694_);
    crate::leanh::lean_ctor_set(v___x_3708_, 4, v_maxRecDepth_3695_);
    crate::leanh::lean_ctor_set(v___x_3708_, 5, v_ref_3707_);
    crate::leanh::lean_ctor_set(v___x_3708_, 6, v_currNamespace_3697_);
    crate::leanh::lean_ctor_set(v___x_3708_, 7, v_openDecls_3698_);
    crate::leanh::lean_ctor_set(v___x_3708_, 8, v_initHeartbeats_3699_);
    crate::leanh::lean_ctor_set(v___x_3708_, 9, v_maxHeartbeats_3700_);
    crate::leanh::lean_ctor_set(v___x_3708_, 10, v_quotContext_3701_);
    crate::leanh::lean_ctor_set(v___x_3708_, 11, v_currMacroScope_3702_);
    crate::leanh::lean_ctor_set(v___x_3708_, 12, v_cancelTk_x3f_3704_);
    crate::leanh::lean_ctor_set(v___x_3708_, 13, v_inheritedTraceOptions_3706_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3708_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3703_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3708_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3705_,
    );
    v___x_3709_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(v_msg_3683_, v___y_3686_, v___y_3687_, v___x_3708_, v___y_3689_);
    crate::leanh::lean_dec_ref_known(v___x_3708_, 14);
    return v___x_3709_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg___boxed(
    mut v_ref_3710_: *mut crate::leanh::LeanObject,
    mut v_msg_3711_: *mut crate::leanh::LeanObject,
    mut v___y_3712_: *mut crate::leanh::LeanObject,
    mut v___y_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3719_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(v_ref_3710_, v_msg_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
    crate::leanh::lean_dec(v___y_3717_);
    crate::leanh::lean_dec_ref(v___y_3716_);
    crate::leanh::lean_dec(v___y_3715_);
    crate::leanh::lean_dec_ref(v___y_3714_);
    crate::leanh::lean_dec(v___y_3713_);
    crate::leanh::lean_dec(v___y_3712_);
    crate::leanh::lean_dec(v_ref_3710_);
    return v_res_3719_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(
    mut v_ref_3720_: *mut crate::leanh::LeanObject,
    mut v_msg_3721_: *mut crate::leanh::LeanObject,
    mut v_declHint_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
    mut v___y_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3730_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17(v_msg_3721_, v_declHint_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
    v_a_3731_ = crate::leanh::lean_ctor_get(v___x_3730_, 0);
    crate::leanh::lean_inc(v_a_3731_);
    crate::leanh::lean_dec_ref(v___x_3730_);
    v___x_3732_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(v_ref_3720_, v_a_3731_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
    return v___x_3732_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg___boxed(
    mut v_ref_3733_: *mut crate::leanh::LeanObject,
    mut v_msg_3734_: *mut crate::leanh::LeanObject,
    mut v_declHint_3735_: *mut crate::leanh::LeanObject,
    mut v___y_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
    mut v___y_3741_: *mut crate::leanh::LeanObject,
    mut v___y_3742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3743_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(v_ref_3733_, v_msg_3734_, v_declHint_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
    crate::leanh::lean_dec(v___y_3741_);
    crate::leanh::lean_dec_ref(v___y_3740_);
    crate::leanh::lean_dec(v___y_3739_);
    crate::leanh::lean_dec_ref(v___y_3738_);
    crate::leanh::lean_dec(v___y_3737_);
    crate::leanh::lean_dec(v___y_3736_);
    crate::leanh::lean_dec(v_ref_3733_);
    return v_res_3743_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3745_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0;
    v___x_3746_ = l_Lean_stringToMessageData(v___x_3745_);
    return v___x_3746_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3748_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2;
    v___x_3749_ = l_Lean_stringToMessageData(v___x_3748_);
    return v___x_3749_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(
    mut v_ref_3750_: *mut crate::leanh::LeanObject,
    mut v_constName_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
    mut v___y_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
    mut v___y_3755_: *mut crate::leanh::LeanObject,
    mut v___y_3756_: *mut crate::leanh::LeanObject,
    mut v___y_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3759_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1);
    v___x_3760_ = 0;
    crate::leanh::lean_inc(v_constName_3751_);
    v___x_3761_ = l_Lean_MessageData_ofConstName(v_constName_3751_, v___x_3760_);
    v___x_3762_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3762_, 0, v___x_3759_);
    crate::leanh::lean_ctor_set(v___x_3762_, 1, v___x_3761_);
    v___x_3763_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3);
    v___x_3764_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3764_, 0, v___x_3762_);
    crate::leanh::lean_ctor_set(v___x_3764_, 1, v___x_3763_);
    v___x_3765_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(v_ref_3750_, v___x_3764_, v_constName_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
    return v___x_3765_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___boxed(
    mut v_ref_3766_: *mut crate::leanh::LeanObject,
    mut v_constName_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
    mut v___y_3771_: *mut crate::leanh::LeanObject,
    mut v___y_3772_: *mut crate::leanh::LeanObject,
    mut v___y_3773_: *mut crate::leanh::LeanObject,
    mut v___y_3774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3775_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(v_ref_3766_, v_constName_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
    crate::leanh::lean_dec(v___y_3773_);
    crate::leanh::lean_dec_ref(v___y_3772_);
    crate::leanh::lean_dec(v___y_3771_);
    crate::leanh::lean_dec_ref(v___y_3770_);
    crate::leanh::lean_dec(v___y_3769_);
    crate::leanh::lean_dec(v___y_3768_);
    crate::leanh::lean_dec(v_ref_3766_);
    return v_res_3775_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(
    mut v_constName_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_3784_ = crate::leanh::lean_ctor_get(v___y_3781_, 5);
    v___x_3785_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(v_ref_3784_, v_constName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
    return v___x_3785_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_constName_3786_: *mut crate::leanh::LeanObject,
    mut v___y_3787_: *mut crate::leanh::LeanObject,
    mut v___y_3788_: *mut crate::leanh::LeanObject,
    mut v___y_3789_: *mut crate::leanh::LeanObject,
    mut v___y_3790_: *mut crate::leanh::LeanObject,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3794_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(v_constName_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
    crate::leanh::lean_dec(v___y_3792_);
    crate::leanh::lean_dec_ref(v___y_3791_);
    crate::leanh::lean_dec(v___y_3790_);
    crate::leanh::lean_dec_ref(v___y_3789_);
    crate::leanh::lean_dec(v___y_3788_);
    crate::leanh::lean_dec(v___y_3787_);
    return v_res_3794_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(
    mut v_constName_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
    mut v___y_3798_: *mut crate::leanh::LeanObject,
    mut v___y_3799_: *mut crate::leanh::LeanObject,
    mut v___y_3800_: *mut crate::leanh::LeanObject,
    mut v___y_3801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3803_ = lean_st_ref_get(v___y_3801_);
                v_env_3804_ = crate::leanh::lean_ctor_get(v___x_3803_, 0);
                crate::leanh::lean_inc_ref(v_env_3804_);
                crate::leanh::lean_dec(v___x_3803_);
                v___x_3805_ = 0;
                crate::leanh::lean_inc(v_constName_3795_);
                v___x_3806_ =
                    l_Lean_Environment_find_x3f(v_env_3804_, v_constName_3795_, v___x_3805_);
                if crate::leanh::lean_obj_tag(v___x_3806_) == 0 {
                    v___x_3807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(v_constName_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
                    return v___x_3807_;
                } else {
                    crate::leanh::lean_dec(v_constName_3795_);
                    v_val_3808_ = crate::leanh::lean_ctor_get(v___x_3806_, 0);
                    v_isSharedCheck_3815_ = (!crate::leanh::lean_is_exclusive(v___x_3806_)) as u8;
                    if v_isSharedCheck_3815_ == 0 {
                        v___x_3810_ = v___x_3806_;
                        v_isShared_3811_ = v_isSharedCheck_3815_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3808_);
                        crate::leanh::lean_dec(v___x_3806_);
                        v___x_3810_ = crate::leanh::lean_box(0);
                        v_isShared_3811_ = v_isSharedCheck_3815_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3811_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3810_, 0);
                    v___x_3813_ = v___x_3810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_val_3808_);
                    v___x_3813_ = v_reuseFailAlloc_3814_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7___boxed(
    mut v_constName_3816_: *mut crate::leanh::LeanObject,
    mut v___y_3817_: *mut crate::leanh::LeanObject,
    mut v___y_3818_: *mut crate::leanh::LeanObject,
    mut v___y_3819_: *mut crate::leanh::LeanObject,
    mut v___y_3820_: *mut crate::leanh::LeanObject,
    mut v___y_3821_: *mut crate::leanh::LeanObject,
    mut v___y_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3824_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(v_constName_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
    crate::leanh::lean_dec(v___y_3822_);
    crate::leanh::lean_dec_ref(v___y_3821_);
    crate::leanh::lean_dec(v___y_3820_);
    crate::leanh::lean_dec_ref(v___y_3819_);
    crate::leanh::lean_dec(v___y_3818_);
    crate::leanh::lean_dec(v___y_3817_);
    return v_res_3824_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3825_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_3825_;
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8(
    mut v_msg_3830_: *mut crate::leanh::LeanObject,
    mut v___y_3831_: *mut crate::leanh::LeanObject,
    mut v___y_3832_: *mut crate::leanh::LeanObject,
    mut v___y_3833_: *mut crate::leanh::LeanObject,
    mut v___y_3834_: *mut crate::leanh::LeanObject,
    mut v___y_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v_toFunctor_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___f_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v_toFunctor_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3874_: u8 = 0;
    let mut v___f_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_27360__overap_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_unused_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_unused_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3901_: u8 = 0;
    let mut v_unused_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_unused_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3838_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0_once), _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0);
                v___x_3839_ = l_StateRefT_x27_instMonad___redArg(v___x_3838_);
                v_toApplicative_3840_ = crate::leanh::lean_ctor_get(v___x_3839_, 0);
                v_isSharedCheck_3903_ = (!crate::leanh::lean_is_exclusive(v___x_3839_)) as u8;
                if v_isSharedCheck_3903_ == 0 {
                    v_unused_3904_ = crate::leanh::lean_ctor_get(v___x_3839_, 1);
                    crate::leanh::lean_dec(v_unused_3904_);
                    v___x_3842_ = v___x_3839_;
                    v_isShared_3843_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3840_);
                    crate::leanh::lean_dec(v___x_3839_);
                    v___x_3842_ = crate::leanh::lean_box(0);
                    v_isShared_3843_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3844_ = crate::leanh::lean_ctor_get(v_toApplicative_3840_, 0);
                v_toSeq_3845_ = crate::leanh::lean_ctor_get(v_toApplicative_3840_, 2);
                v_toSeqLeft_3846_ = crate::leanh::lean_ctor_get(v_toApplicative_3840_, 3);
                v_toSeqRight_3847_ = crate::leanh::lean_ctor_get(v_toApplicative_3840_, 4);
                v_isSharedCheck_3901_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3840_)) as u8;
                if v_isSharedCheck_3901_ == 0 {
                    v_unused_3902_ = crate::leanh::lean_ctor_get(v_toApplicative_3840_, 1);
                    crate::leanh::lean_dec(v_unused_3902_);
                    v___x_3849_ = v_toApplicative_3840_;
                    v_isShared_3850_ = v_isSharedCheck_3901_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3847_);
                    crate::leanh::lean_inc(v_toSeqLeft_3846_);
                    crate::leanh::lean_inc(v_toSeq_3845_);
                    crate::leanh::lean_inc(v_toFunctor_3844_);
                    crate::leanh::lean_dec(v_toApplicative_3840_);
                    v___x_3849_ = crate::leanh::lean_box(0);
                    v_isShared_3850_ = v_isSharedCheck_3901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3851_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1;
                v___f_3852_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2;
                crate::leanh::lean_inc_ref(v_toFunctor_3844_);
                v___f_3853_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3853_, 0, v_toFunctor_3844_);
                v___f_3854_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3854_, 0, v_toFunctor_3844_);
                v___x_3855_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3855_, 0, v___f_3853_);
                crate::leanh::lean_ctor_set(v___x_3855_, 1, v___f_3854_);
                v___f_3856_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3856_, 0, v_toSeqRight_3847_);
                v___f_3857_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3857_, 0, v_toSeqLeft_3846_);
                v___f_3858_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3858_, 0, v_toSeq_3845_);
                if v_isShared_3850_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3849_, 4, v___f_3856_);
                    crate::leanh::lean_ctor_set(v___x_3849_, 3, v___f_3857_);
                    crate::leanh::lean_ctor_set(v___x_3849_, 2, v___f_3858_);
                    crate::leanh::lean_ctor_set(v___x_3849_, 1, v___f_3851_);
                    crate::leanh::lean_ctor_set(v___x_3849_, 0, v___x_3855_);
                    v___x_3860_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3900_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___f_3851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 2, v___f_3858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 3, v___f_3857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 4, v___f_3856_);
                    v___x_3860_ = v_reuseFailAlloc_3900_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3842_, 1, v___f_3852_);
                    crate::leanh::lean_ctor_set(v___x_3842_, 0, v___x_3860_);
                    v___x_3862_ = v___x_3842_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3860_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___f_3852_);
                    v___x_3862_ = v_reuseFailAlloc_3899_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3863_ = l_StateRefT_x27_instMonad___redArg(v___x_3862_);
                v_toApplicative_3864_ = crate::leanh::lean_ctor_get(v___x_3863_, 0);
                v_isSharedCheck_3897_ = (!crate::leanh::lean_is_exclusive(v___x_3863_)) as u8;
                if v_isSharedCheck_3897_ == 0 {
                    v_unused_3898_ = crate::leanh::lean_ctor_get(v___x_3863_, 1);
                    crate::leanh::lean_dec(v_unused_3898_);
                    v___x_3866_ = v___x_3863_;
                    v_isShared_3867_ = v_isSharedCheck_3897_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_3864_);
                    crate::leanh::lean_dec(v___x_3863_);
                    v___x_3866_ = crate::leanh::lean_box(0);
                    v_isShared_3867_ = v_isSharedCheck_3897_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3868_ = crate::leanh::lean_ctor_get(v_toApplicative_3864_, 0);
                v_toSeq_3869_ = crate::leanh::lean_ctor_get(v_toApplicative_3864_, 2);
                v_toSeqLeft_3870_ = crate::leanh::lean_ctor_get(v_toApplicative_3864_, 3);
                v_toSeqRight_3871_ = crate::leanh::lean_ctor_get(v_toApplicative_3864_, 4);
                v_isSharedCheck_3895_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_3864_)) as u8;
                if v_isSharedCheck_3895_ == 0 {
                    v_unused_3896_ = crate::leanh::lean_ctor_get(v_toApplicative_3864_, 1);
                    crate::leanh::lean_dec(v_unused_3896_);
                    v___x_3873_ = v_toApplicative_3864_;
                    v_isShared_3874_ = v_isSharedCheck_3895_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_3871_);
                    crate::leanh::lean_inc(v_toSeqLeft_3870_);
                    crate::leanh::lean_inc(v_toSeq_3869_);
                    crate::leanh::lean_inc(v_toFunctor_3868_);
                    crate::leanh::lean_dec(v_toApplicative_3864_);
                    v___x_3873_ = crate::leanh::lean_box(0);
                    v_isShared_3874_ = v_isSharedCheck_3895_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3875_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3;
                v___f_3876_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4;
                crate::leanh::lean_inc_ref(v_toFunctor_3868_);
                v___f_3877_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3877_, 0, v_toFunctor_3868_);
                v___f_3878_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3878_, 0, v_toFunctor_3868_);
                v___x_3879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3879_, 0, v___f_3877_);
                crate::leanh::lean_ctor_set(v___x_3879_, 1, v___f_3878_);
                v___f_3880_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3880_, 0, v_toSeqRight_3871_);
                v___f_3881_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3881_, 0, v_toSeqLeft_3870_);
                v___f_3882_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_3882_, 0, v_toSeq_3869_);
                if v_isShared_3874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3873_, 4, v___f_3880_);
                    crate::leanh::lean_ctor_set(v___x_3873_, 3, v___f_3881_);
                    crate::leanh::lean_ctor_set(v___x_3873_, 2, v___f_3882_);
                    crate::leanh::lean_ctor_set(v___x_3873_, 1, v___f_3875_);
                    crate::leanh::lean_ctor_set(v___x_3873_, 0, v___x_3879_);
                    v___x_3884_ = v___x_3873_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 1, v___f_3875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 2, v___f_3882_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 3, v___f_3881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 4, v___f_3880_);
                    v___x_3884_ = v_reuseFailAlloc_3894_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3867_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3866_, 1, v___f_3876_);
                    crate::leanh::lean_ctor_set(v___x_3866_, 0, v___x_3884_);
                    v___x_3886_ = v___x_3866_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3893_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___f_3876_);
                    v___x_3886_ = v_reuseFailAlloc_3893_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3887_ = l_StateRefT_x27_instMonad___redArg(v___x_3886_);
                v___x_3888_ = l_StateRefT_x27_instMonad___redArg(v___x_3887_);
                v___x_3889_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
                v___x_3890_ = l_instInhabitedOfMonad___redArg(v___x_3888_, v___x_3889_);
                v___x_27360__overap_3891_ = lean_panic_fn_borrowed(v___x_3890_, v_msg_3830_);
                crate::leanh::lean_dec(v___x_3890_);
                crate::leanh::lean_inc(v___y_3836_);
                crate::leanh::lean_inc_ref(v___y_3835_);
                crate::leanh::lean_inc(v___y_3834_);
                crate::leanh::lean_inc_ref(v___y_3833_);
                crate::leanh::lean_inc(v___y_3832_);
                crate::leanh::lean_inc(v___y_3831_);
                v___x_3892_ = crate::leanh::lean_apply_7(
                    v___x_27360__overap_3891_,
                    v___y_3831_,
                    v___y_3832_,
                    v___y_3833_,
                    v___y_3834_,
                    v___y_3835_,
                    v___y_3836_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___boxed(
    mut v_msg_3905_: *mut crate::leanh::LeanObject,
    mut v___y_3906_: *mut crate::leanh::LeanObject,
    mut v___y_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
    mut v___y_3909_: *mut crate::leanh::LeanObject,
    mut v___y_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
    mut v___y_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8(v_msg_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    crate::leanh::lean_dec(v___y_3911_);
    crate::leanh::lean_dec_ref(v___y_3910_);
    crate::leanh::lean_dec(v___y_3909_);
    crate::leanh::lean_dec_ref(v___y_3908_);
    crate::leanh::lean_dec(v___y_3907_);
    crate::leanh::lean_dec(v___y_3906_);
    return v_res_3913_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2;
    v___x_3918_ = crate::leanh::lean_unsigned_to_nat(53);
    v___x_3919_ = crate::leanh::lean_unsigned_to_nat(62);
    v___x_3920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__1;
    v___x_3921_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__0;
    v___x_3922_ = l_mkPanicMessageWithDecl(
        v___x_3921_,
        v___x_3920_,
        v___x_3919_,
        v___x_3918_,
        v___x_3917_,
    );
    return v___x_3922_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10(
    mut v_sz_3923_: usize,
    mut v_i_3924_: usize,
    mut v_bs_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v___y_3931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: usize = 0;
    let mut v___x_3943_: usize = 0;
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: u8 = 0;
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut v_a_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3933_ = lean_usize_dec_lt(v_i_3924_, v_sz_3923_);
                if v___x_3933_ == 0 {
                    v___x_3934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3934_, 0, v_bs_3925_);
                    return v___x_3934_;
                } else {
                    v_v_3935_ = lean_array_uget_borrowed(v_bs_3925_, v_i_3924_);
                    crate::leanh::lean_inc(v_v_3935_);
                    v___x_3936_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(v_v_3935_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
                    if crate::leanh::lean_obj_tag(v___x_3936_) == 0 {
                        v_a_3937_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                        crate::leanh::lean_inc(v_a_3937_);
                        crate::leanh::lean_dec_ref_known(v___x_3936_, 1);
                        v___x_3938_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3939_ = lean_array_uset(v_bs_3925_, v_i_3924_, v___x_3938_);
                        if crate::leanh::lean_obj_tag(v_a_3937_) == 6 {
                            v_val_3946_ = crate::leanh::lean_ctor_get(v_a_3937_, 0);
                            crate::leanh::lean_inc_ref(v_val_3946_);
                            crate::leanh::lean_dec_ref_known(v_a_3937_, 1);
                            v_numFields_3947_ = crate::leanh::lean_ctor_get(v_val_3946_, 4);
                            crate::leanh::lean_inc(v_numFields_3947_);
                            crate::leanh::lean_dec_ref(v_val_3946_);
                            v___x_3948_ = 0;
                            v___x_3949_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            crate::leanh::lean_ctor_set(v___x_3949_, 0, v_numFields_3947_);
                            crate::leanh::lean_ctor_set(v___x_3949_, 1, v___x_3938_);
                            crate::leanh::lean_ctor_set_uint8(
                                v___x_3949_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                                v___x_3948_,
                            );
                            v_a_3941_ = v___x_3949_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3937_);
                            v___x_3950_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3);
                            v___x_3951_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8(v___x_3950_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
                            if crate::leanh::lean_obj_tag(v___x_3951_) == 0 {
                                v_a_3952_ = crate::leanh::lean_ctor_get(v___x_3951_, 0);
                                crate::leanh::lean_inc(v_a_3952_);
                                crate::leanh::lean_dec_ref_known(v___x_3951_, 1);
                                v_a_3941_ = v_a_3952_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_bs_x27_3939_);
                                v_a_3953_ = crate::leanh::lean_ctor_get(v___x_3951_, 0);
                                v_isSharedCheck_3960_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3951_)) as u8;
                                if v_isSharedCheck_3960_ == 0 {
                                    v___x_3955_ = v___x_3951_;
                                    v_isShared_3956_ = v_isSharedCheck_3960_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3953_);
                                    crate::leanh::lean_dec(v___x_3951_);
                                    v___x_3955_ = crate::leanh::lean_box(0);
                                    v_isShared_3956_ = v_isSharedCheck_3960_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_3925_);
                        v_a_3961_ = crate::leanh::lean_ctor_get(v___x_3936_, 0);
                        v_isSharedCheck_3968_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3936_)) as u8;
                        if v_isSharedCheck_3968_ == 0 {
                            v___x_3963_ = v___x_3936_;
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3961_);
                            crate::leanh::lean_dec(v___x_3936_);
                            v___x_3963_ = crate::leanh::lean_box(0);
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3942_ = 1usize;
                v___x_3943_ = lean_usize_add(v_i_3924_, v___x_3942_);
                v___x_3944_ = lean_array_uset(v_bs_x27_3939_, v_i_3924_, v_a_3941_);
                v_i_3924_ = v___x_3943_;
                v_bs_3925_ = v___x_3944_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_3956_ == 0 {
                    v___x_3958_ = v___x_3955_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
                    v___x_3958_ = v_reuseFailAlloc_3959_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3958_;
            }
            4 => {
                if v_isShared_3964_ == 0 {
                    v___x_3966_ = v___x_3963_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___boxed(
    mut v_sz_3969_: *mut crate::leanh::LeanObject,
    mut v_i_3970_: *mut crate::leanh::LeanObject,
    mut v_bs_3971_: *mut crate::leanh::LeanObject,
    mut v___y_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3979_: usize = 0;
    let mut v_i_boxed_3980_: usize = 0;
    let mut v_res_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3979_ = crate::leanh::lean_unbox_usize(v_sz_3969_);
    crate::leanh::lean_dec(v_sz_3969_);
    v_i_boxed_3980_ = crate::leanh::lean_unbox_usize(v_i_3970_);
    crate::leanh::lean_dec(v_i_3970_);
    v_res_3981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10(v_sz_boxed_3979_, v_i_boxed_3980_, v_bs_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
    crate::leanh::lean_dec(v___y_3977_);
    crate::leanh::lean_dec_ref(v___y_3976_);
    crate::leanh::lean_dec(v___y_3975_);
    crate::leanh::lean_dec_ref(v___y_3974_);
    crate::leanh::lean_dec(v___y_3973_);
    crate::leanh::lean_dec(v___y_3972_);
    return v_res_3981_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(
    mut v_declName_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3985_ = lean_st_ref_get(v___y_3983_);
    v_env_3986_ = crate::leanh::lean_ctor_get(v___x_3985_, 0);
    crate::leanh::lean_inc_ref(v_env_3986_);
    crate::leanh::lean_dec(v___x_3985_);
    v___x_3987_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3986_, v_declName_3982_);
    v___x_3988_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3988_, 0, v___x_3987_);
    return v___x_3988_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg___boxed(
    mut v_declName_3989_: *mut crate::leanh::LeanObject,
    mut v___y_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3992_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(v_declName_3989_, v___y_3990_);
    crate::leanh::lean_dec(v___y_3990_);
    return v_res_3992_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3993_ = crate::leanh::lean_box(0);
    v___x_3994_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3995_ = lean_mk_array(v___x_3994_, v___x_3993_);
    return v___x_3995_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3996_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0);
    v___x_3997_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3998_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3998_, 0, v___x_3997_);
    crate::leanh::lean_ctor_set(v___x_3998_, 1, v___x_3996_);
    return v___x_3998_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5(
    mut v_e_4001_: *mut crate::leanh::LeanObject,
    mut v_alsoCasesOn_4002_: u8,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v_val_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v_dummy_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: u8 = 0;
    let mut v_numParams_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    let mut v_indName_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4075_: u8 = 0;
    let mut v_val_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v_toConstantVal_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4114_: usize = 0;
    let mut v___x_4115_: usize = 0;
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v_start_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut v_a_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v_lower_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: u8 = 0;
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v_a_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut v_isSharedCheck_4174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4013_ = l_Lean_Expr_isApp(v_e_4001_);
                if v___x_4013_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_4001_);
                    v___x_4014_ = crate::leanh::lean_box(0);
                    v___x_4015_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4015_, 0, v___x_4014_);
                    return v___x_4015_;
                } else {
                    v___x_4016_ = l_Lean_Expr_getAppFn(v_e_4001_);
                    if crate::leanh::lean_obj_tag(v___x_4016_) == 4 {
                        v_declName_4017_ = crate::leanh::lean_ctor_get(v___x_4016_, 0);
                        crate::leanh::lean_inc_n(v_declName_4017_, 2);
                        v_us_4018_ = crate::leanh::lean_ctor_get(v___x_4016_, 1);
                        crate::leanh::lean_inc(v_us_4018_);
                        crate::leanh::lean_dec_ref_known(v___x_4016_, 2);
                        v___x_4019_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(v_declName_4017_, v___y_4008_);
                        v_a_4020_ = crate::leanh::lean_ctor_get(v___x_4019_, 0);
                        v_isSharedCheck_4174_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4019_)) as u8;
                        if v_isSharedCheck_4174_ == 0 {
                            v___x_4022_ = v___x_4019_;
                            v_isShared_4023_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4020_);
                            crate::leanh::lean_dec(v___x_4019_);
                            v___x_4022_ = crate::leanh::lean_box(0);
                            v_isShared_4023_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4016_);
                        crate::leanh::lean_dec_ref(v_e_4001_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4011_ = crate::leanh::lean_box(0);
                v___x_4012_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4012_, 0, v___x_4011_);
                return v___x_4012_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4020_) == 1 {
                    v_val_4024_ = crate::leanh::lean_ctor_get(v_a_4020_, 0);
                    v_isSharedCheck_4066_ = (!crate::leanh::lean_is_exclusive(v_a_4020_)) as u8;
                    if v_isSharedCheck_4066_ == 0 {
                        v___x_4026_ = v_a_4020_;
                        v_isShared_4027_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4024_);
                        crate::leanh::lean_dec(v_a_4020_);
                        v___x_4026_ = crate::leanh::lean_box(0);
                        v_isShared_4027_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4022_);
                    crate::leanh::lean_dec(v_a_4020_);
                    v___x_4067_ = lean_st_ref_get(v___y_4008_);
                    if v_alsoCasesOn_4002_ == 0 {
                        crate::leanh::lean_dec(v___x_4067_);
                        crate::leanh::lean_dec(v_us_4018_);
                        crate::leanh::lean_dec(v_declName_4017_);
                        crate::leanh::lean_dec_ref(v_e_4001_);
                        state = 1;
                        continue;
                    } else {
                        v_env_4068_ = crate::leanh::lean_ctor_get(v___x_4067_, 0);
                        crate::leanh::lean_inc_ref(v_env_4068_);
                        crate::leanh::lean_dec(v___x_4067_);
                        crate::leanh::lean_inc(v_declName_4017_);
                        v___x_4069_ = l_Lean_isCasesOnRecursor(v_env_4068_, v_declName_4017_);
                        if v___x_4069_ == 0 {
                            crate::leanh::lean_dec(v_us_4018_);
                            crate::leanh::lean_dec(v_declName_4017_);
                            crate::leanh::lean_dec_ref(v_e_4001_);
                            state = 1;
                            continue;
                        } else {
                            v_indName_4070_ = l_Lean_Name_getPrefix(v_declName_4017_);
                            v___x_4071_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(v_indName_4070_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
                            if crate::leanh::lean_obj_tag(v___x_4071_) == 0 {
                                v_a_4072_ = crate::leanh::lean_ctor_get(v___x_4071_, 0);
                                v_isSharedCheck_4165_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4071_)) as u8;
                                if v_isSharedCheck_4165_ == 0 {
                                    v___x_4074_ = v___x_4071_;
                                    v_isShared_4075_ = v_isSharedCheck_4165_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4072_);
                                    crate::leanh::lean_dec(v___x_4071_);
                                    v___x_4074_ = crate::leanh::lean_box(0);
                                    v_isShared_4075_ = v_isSharedCheck_4165_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_us_4018_);
                                crate::leanh::lean_dec(v_declName_4017_);
                                crate::leanh::lean_dec_ref(v_e_4001_);
                                v_a_4166_ = crate::leanh::lean_ctor_get(v___x_4071_, 0);
                                v_isSharedCheck_4173_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4071_)) as u8;
                                if v_isSharedCheck_4173_ == 0 {
                                    v___x_4168_ = v___x_4071_;
                                    v_isShared_4169_ = v_isSharedCheck_4173_;
                                    state = 18;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4166_);
                                    crate::leanh::lean_dec(v___x_4071_);
                                    v___x_4168_ = crate::leanh::lean_box(0);
                                    v_isShared_4169_ = v_isSharedCheck_4173_;
                                    state = 18;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v_dummy_4028_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                v_nargs_4029_ = l_Lean_Expr_getAppNumArgs(v_e_4001_);
                crate::leanh::lean_inc(v_nargs_4029_);
                v___x_4030_ = lean_mk_array(v_nargs_4029_, v_dummy_4028_);
                v___x_4031_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4032_ = lean_nat_sub(v_nargs_4029_, v___x_4031_);
                crate::leanh::lean_dec(v_nargs_4029_);
                v_args_4033_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_4001_,
                    v___x_4030_,
                    v___x_4032_,
                );
                v___x_4034_ = lean_array_get_size(v_args_4033_);
                v___x_4035_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_4024_);
                v___x_4036_ = lean_nat_dec_lt(v___x_4034_, v___x_4035_);
                crate::leanh::lean_dec(v___x_4035_);
                if v___x_4036_ == 0 {
                    v_numParams_4037_ = crate::leanh::lean_ctor_get(v_val_4024_, 0);
                    v_numDiscrs_4038_ = crate::leanh::lean_ctor_get(v_val_4024_, 1);
                    v___x_4039_ = lean_array_mk(v_us_4018_);
                    v___x_4040_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_numParams_4037_);
                    v___x_4041_ =
                        l_Array_extract___redArg(v_args_4033_, v___x_4040_, v_numParams_4037_);
                    v___x_4042_ = l_Lean_instInhabitedExpr;
                    v___x_4043_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_4024_);
                    v___x_4044_ = lean_array_get(v___x_4042_, v_args_4033_, v___x_4043_);
                    crate::leanh::lean_dec(v___x_4043_);
                    v___x_4045_ = lean_nat_add(v_numParams_4037_, v___x_4031_);
                    v___x_4046_ = lean_nat_add(v___x_4045_, v_numDiscrs_4038_);
                    crate::leanh::lean_inc(v___x_4046_);
                    crate::leanh::lean_inc_ref_n(v_args_4033_, 2);
                    v___x_4047_ =
                        l_Array_toSubarray___redArg(v_args_4033_, v___x_4045_, v___x_4046_);
                    v___x_4048_ = l_Subarray_copy___redArg(v___x_4047_);
                    v___x_4049_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_4024_);
                    v___x_4050_ = lean_nat_add(v___x_4046_, v___x_4049_);
                    crate::leanh::lean_dec(v___x_4049_);
                    crate::leanh::lean_inc(v___x_4050_);
                    v___x_4051_ =
                        l_Array_toSubarray___redArg(v_args_4033_, v___x_4046_, v___x_4050_);
                    v___x_4052_ = l_Subarray_copy___redArg(v___x_4051_);
                    v___x_4053_ =
                        l_Array_toSubarray___redArg(v_args_4033_, v___x_4050_, v___x_4034_);
                    v___x_4054_ = l_Subarray_copy___redArg(v___x_4053_);
                    v___x_4055_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4055_, 0, v_val_4024_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 1, v_declName_4017_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 2, v___x_4039_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 3, v___x_4041_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 4, v___x_4044_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 5, v___x_4048_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 6, v___x_4052_);
                    crate::leanh::lean_ctor_set(v___x_4055_, 7, v___x_4054_);
                    if v_isShared_4027_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4026_, 0, v___x_4055_);
                        v___x_4057_ = v___x_4026_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4055_);
                        v___x_4057_ = v_reuseFailAlloc_4061_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_4033_);
                    crate::leanh::lean_del_object(v___x_4026_);
                    crate::leanh::lean_dec(v_val_4024_);
                    crate::leanh::lean_dec(v_us_4018_);
                    crate::leanh::lean_dec(v_declName_4017_);
                    v___x_4062_ = crate::leanh::lean_box(0);
                    if v_isShared_4023_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4022_, 0, v___x_4062_);
                        v___x_4064_ = v___x_4022_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4065_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
                        v___x_4064_ = v_reuseFailAlloc_4065_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4023_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4022_, 0, v___x_4057_);
                    v___x_4059_ = v___x_4022_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
                    v___x_4059_ = v_reuseFailAlloc_4060_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4059_;
            }
            6 => {
                return v___x_4064_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_4072_) == 5 {
                    v_val_4076_ = crate::leanh::lean_ctor_get(v_a_4072_, 0);
                    v_isSharedCheck_4160_ = (!crate::leanh::lean_is_exclusive(v_a_4072_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4078_ = v_a_4072_;
                        v_isShared_4079_ = v_isSharedCheck_4160_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4076_);
                        crate::leanh::lean_dec(v_a_4072_);
                        v___x_4078_ = crate::leanh::lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4160_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4072_);
                    crate::leanh::lean_dec(v_us_4018_);
                    crate::leanh::lean_dec(v_declName_4017_);
                    crate::leanh::lean_dec_ref(v_e_4001_);
                    v___x_4161_ = crate::leanh::lean_box(0);
                    if v_isShared_4075_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4074_, 0, v___x_4161_);
                        v___x_4163_ = v___x_4074_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4161_);
                        v___x_4163_ = v_reuseFailAlloc_4164_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                v_toConstantVal_4080_ = crate::leanh::lean_ctor_get(v_val_4076_, 0);
                crate::leanh::lean_inc_ref(v_toConstantVal_4080_);
                v_numParams_4081_ = crate::leanh::lean_ctor_get(v_val_4076_, 1);
                crate::leanh::lean_inc(v_numParams_4081_);
                v_numIndices_4082_ = crate::leanh::lean_ctor_get(v_val_4076_, 2);
                crate::leanh::lean_inc(v_numIndices_4082_);
                v_ctors_4083_ = crate::leanh::lean_ctor_get(v_val_4076_, 4);
                crate::leanh::lean_inc(v_ctors_4083_);
                v_nargs_4084_ = l_Lean_Expr_getAppNumArgs(v_e_4001_);
                v_dummy_4085_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                crate::leanh::lean_inc(v_nargs_4084_);
                v___x_4086_ = lean_mk_array(v_nargs_4084_, v_dummy_4085_);
                v___x_4087_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4088_ = lean_nat_sub(v_nargs_4084_, v___x_4087_);
                crate::leanh::lean_dec(v_nargs_4084_);
                v_args_4089_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_4001_,
                    v___x_4086_,
                    v___x_4088_,
                );
                v___x_4090_ = lean_nat_add(v_numParams_4081_, v___x_4087_);
                v___x_4091_ = lean_nat_add(v___x_4090_, v_numIndices_4082_);
                v___x_4092_ = lean_nat_add(v___x_4091_, v___x_4087_);
                crate::leanh::lean_dec(v___x_4091_);
                v___x_4093_ = l_Lean_InductiveVal_numCtors(v_val_4076_);
                crate::leanh::lean_dec_ref(v_val_4076_);
                v___x_4094_ = lean_nat_add(v___x_4092_, v___x_4093_);
                crate::leanh::lean_dec(v___x_4093_);
                v___x_4095_ = lean_array_get_size(v_args_4089_);
                v___x_4096_ = lean_nat_dec_le(v___x_4094_, v___x_4095_);
                if v___x_4096_ == 0 {
                    crate::leanh::lean_dec(v___x_4094_);
                    crate::leanh::lean_dec(v___x_4092_);
                    crate::leanh::lean_dec(v___x_4090_);
                    crate::leanh::lean_dec_ref(v_args_4089_);
                    crate::leanh::lean_dec(v_ctors_4083_);
                    crate::leanh::lean_dec(v_numIndices_4082_);
                    crate::leanh::lean_dec(v_numParams_4081_);
                    crate::leanh::lean_dec_ref(v_toConstantVal_4080_);
                    crate::leanh::lean_del_object(v___x_4078_);
                    crate::leanh::lean_dec(v_us_4018_);
                    crate::leanh::lean_dec(v_declName_4017_);
                    v___x_4097_ = crate::leanh::lean_box(0);
                    if v_isShared_4075_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4074_, 0, v___x_4097_);
                        v___x_4099_ = v___x_4074_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4100_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4097_);
                        v___x_4099_ = v_reuseFailAlloc_4100_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4074_);
                    v___x_4101_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_numParams_4081_);
                    crate::leanh::lean_inc_ref_n(v_args_4089_, 3);
                    v_params_4102_ =
                        l_Array_toSubarray___redArg(v_args_4089_, v___x_4101_, v_numParams_4081_);
                    v___x_4103_ = l_Lean_instInhabitedExpr;
                    v_motive_4104_ = lean_array_get(v___x_4103_, v_args_4089_, v_numParams_4081_);
                    crate::leanh::lean_dec(v_numParams_4081_);
                    crate::leanh::lean_inc(v___x_4092_);
                    v_discrs_4105_ =
                        l_Array_toSubarray___redArg(v_args_4089_, v___x_4090_, v___x_4092_);
                    v___x_4106_ = lean_nat_add(v_numIndices_4082_, v___x_4087_);
                    crate::leanh::lean_dec(v_numIndices_4082_);
                    v___x_4107_ = crate::leanh::lean_box(0);
                    v_discrInfos_4108_ = lean_mk_array(v___x_4106_, v___x_4107_);
                    crate::leanh::lean_inc(v___x_4094_);
                    v_alts_4109_ =
                        l_Array_toSubarray___redArg(v_args_4089_, v___x_4092_, v___x_4094_);
                    v___x_4159_ = lean_nat_dec_le(v___x_4094_, v___x_4101_);
                    if v___x_4159_ == 0 {
                        v_lower_4151_ = v___x_4094_;
                        v_upper_4152_ = v___x_4095_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4094_);
                        v_lower_4151_ = v___x_4101_;
                        v_upper_4152_ = v___x_4095_;
                        state = 16;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_4099_;
            }
            10 => {
                v___x_4113_ = lean_array_mk(v_ctors_4083_);
                v_sz_4114_ = lean_array_size(v___x_4113_);
                v___x_4115_ = 0usize;
                v___x_4116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10(v_sz_4114_, v___x_4115_, v___x_4113_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
                if crate::leanh::lean_obj_tag(v___x_4116_) == 0 {
                    v_a_4117_ = crate::leanh::lean_ctor_get(v___x_4116_, 0);
                    v_isSharedCheck_4141_ = (!crate::leanh::lean_is_exclusive(v___x_4116_)) as u8;
                    if v_isSharedCheck_4141_ == 0 {
                        v___x_4119_ = v___x_4116_;
                        v_isShared_4120_ = v_isSharedCheck_4141_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4117_);
                        crate::leanh::lean_dec(v___x_4116_);
                        v___x_4119_ = crate::leanh::lean_box(0);
                        v_isShared_4120_ = v_isSharedCheck_4141_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4112_);
                    crate::leanh::lean_dec_ref(v___y_4111_);
                    crate::leanh::lean_dec_ref(v_alts_4109_);
                    crate::leanh::lean_dec_ref(v_discrInfos_4108_);
                    crate::leanh::lean_dec_ref(v_discrs_4105_);
                    crate::leanh::lean_dec(v_motive_4104_);
                    crate::leanh::lean_dec_ref(v_params_4102_);
                    crate::leanh::lean_del_object(v___x_4078_);
                    crate::leanh::lean_dec(v_us_4018_);
                    crate::leanh::lean_dec(v_declName_4017_);
                    v_a_4142_ = crate::leanh::lean_ctor_get(v___x_4116_, 0);
                    v_isSharedCheck_4149_ = (!crate::leanh::lean_is_exclusive(v___x_4116_)) as u8;
                    if v_isSharedCheck_4149_ == 0 {
                        v___x_4144_ = v___x_4116_;
                        v_isShared_4145_ = v_isSharedCheck_4149_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4142_);
                        crate::leanh::lean_dec(v___x_4116_);
                        v___x_4144_ = crate::leanh::lean_box(0);
                        v_isShared_4145_ = v_isSharedCheck_4149_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_start_4121_ = crate::leanh::lean_ctor_get(v_params_4102_, 1);
                crate::leanh::lean_inc(v_start_4121_);
                v_stop_4122_ = crate::leanh::lean_ctor_get(v_params_4102_, 2);
                crate::leanh::lean_inc(v_stop_4122_);
                v_start_4123_ = crate::leanh::lean_ctor_get(v_discrs_4105_, 1);
                crate::leanh::lean_inc(v_start_4123_);
                v_stop_4124_ = crate::leanh::lean_ctor_get(v_discrs_4105_, 2);
                crate::leanh::lean_inc(v_stop_4124_);
                v___x_4125_ = lean_nat_sub(v_stop_4122_, v_start_4121_);
                crate::leanh::lean_dec(v_start_4121_);
                crate::leanh::lean_dec(v_stop_4122_);
                v___x_4126_ = lean_nat_sub(v_stop_4124_, v_start_4123_);
                crate::leanh::lean_dec(v_start_4123_);
                crate::leanh::lean_dec(v_stop_4124_);
                v___x_4127_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1);
                v___x_4128_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4128_, 0, v___x_4125_);
                crate::leanh::lean_ctor_set(v___x_4128_, 1, v___x_4126_);
                crate::leanh::lean_ctor_set(v___x_4128_, 2, v_a_4117_);
                crate::leanh::lean_ctor_set(v___x_4128_, 3, v___y_4112_);
                crate::leanh::lean_ctor_set(v___x_4128_, 4, v_discrInfos_4108_);
                crate::leanh::lean_ctor_set(v___x_4128_, 5, v___x_4127_);
                v___x_4129_ = lean_array_mk(v_us_4018_);
                v___x_4130_ = l_Subarray_copy___redArg(v_params_4102_);
                v___x_4131_ = l_Subarray_copy___redArg(v_discrs_4105_);
                v___x_4132_ = l_Subarray_copy___redArg(v_alts_4109_);
                v___x_4133_ = l_Subarray_copy___redArg(v___y_4111_);
                v___x_4134_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4128_);
                crate::leanh::lean_ctor_set(v___x_4134_, 1, v_declName_4017_);
                crate::leanh::lean_ctor_set(v___x_4134_, 2, v___x_4129_);
                crate::leanh::lean_ctor_set(v___x_4134_, 3, v___x_4130_);
                crate::leanh::lean_ctor_set(v___x_4134_, 4, v_motive_4104_);
                crate::leanh::lean_ctor_set(v___x_4134_, 5, v___x_4131_);
                crate::leanh::lean_ctor_set(v___x_4134_, 6, v___x_4132_);
                crate::leanh::lean_ctor_set(v___x_4134_, 7, v___x_4133_);
                if v_isShared_4079_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4078_, 1);
                    crate::leanh::lean_ctor_set(v___x_4078_, 0, v___x_4134_);
                    v___x_4136_ = v___x_4078_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4134_);
                    v___x_4136_ = v_reuseFailAlloc_4140_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4120_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4119_, 0, v___x_4136_);
                    v___x_4138_ = v___x_4119_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4138_;
            }
            14 => {
                if v_isShared_4145_ == 0 {
                    v___x_4147_ = v___x_4144_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4148_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
                    v___x_4147_ = v_reuseFailAlloc_4148_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4147_;
            }
            16 => {
                v_levelParams_4153_ = crate::leanh::lean_ctor_get(v_toConstantVal_4080_, 1);
                crate::leanh::lean_inc(v_levelParams_4153_);
                crate::leanh::lean_dec_ref(v_toConstantVal_4080_);
                v___x_4154_ =
                    l_Array_toSubarray___redArg(v_args_4089_, v_lower_4151_, v_upper_4152_);
                v___x_4155_ = l_List_lengthTR___redArg(v_levelParams_4153_);
                crate::leanh::lean_dec(v_levelParams_4153_);
                v___x_4156_ = l_List_lengthTR___redArg(v_us_4018_);
                v___x_4157_ = lean_nat_dec_eq(v___x_4155_, v___x_4156_);
                crate::leanh::lean_dec(v___x_4156_);
                crate::leanh::lean_dec(v___x_4155_);
                if v___x_4157_ == 0 {
                    v___x_4158_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__2;
                    v___y_4111_ = v___x_4154_;
                    v___y_4112_ = v___x_4158_;
                    state = 10;
                    continue;
                } else {
                    v___y_4111_ = v___x_4154_;
                    v___y_4112_ = v___x_4107_;
                    state = 10;
                    continue;
                }
            }
            17 => {
                return v___x_4163_;
            }
            18 => {
                if v_isShared_4169_ == 0 {
                    v___x_4171_ = v___x_4168_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
                    v___x_4171_ = v_reuseFailAlloc_4172_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4171_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___boxed(
    mut v_e_4175_: *mut crate::leanh::LeanObject,
    mut v_alsoCasesOn_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_alsoCasesOn_boxed_4184_: u8 = 0;
    let mut v_res_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_4184_ = (crate::leanh::lean_unbox(v_alsoCasesOn_4176_) as u8);
    v_res_4185_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5(v_e_4175_, v_alsoCasesOn_boxed_4184_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
    crate::leanh::lean_dec(v___y_4182_);
    crate::leanh::lean_dec_ref(v___y_4181_);
    crate::leanh::lean_dec(v___y_4180_);
    crate::leanh::lean_dec_ref(v___y_4179_);
    crate::leanh::lean_dec(v___y_4178_);
    crate::leanh::lean_dec(v___y_4177_);
    return v_res_4185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0(
    mut v_recArgInfos_4186_: *mut crate::leanh::LeanObject,
    mut v_positions_4187_: *mut crate::leanh::LeanObject,
    mut v_params_4188_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4189_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4190_: *mut crate::leanh::LeanObject,
    mut v_ctx_4191_: *mut crate::leanh::LeanObject,
    mut v_sz_4192_: usize,
    mut v_i_4193_: usize,
    mut v_bs_4194_: *mut crate::leanh::LeanObject,
    mut v___y_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4202_: u8 = 0;
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: usize = 0;
    let mut v___x_4210_: usize = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4202_ = lean_usize_dec_lt(v_i_4193_, v_sz_4192_);
                if v___x_4202_ == 0 {
                    crate::leanh::lean_dec_ref(v_ctx_4191_);
                    crate::leanh::lean_dec_ref(v_containsRecFn_4190_);
                    crate::leanh::lean_dec_ref(v_recFnNames_4189_);
                    crate::leanh::lean_dec_ref(v_params_4188_);
                    crate::leanh::lean_dec_ref(v_positions_4187_);
                    crate::leanh::lean_dec_ref(v_recArgInfos_4186_);
                    v___x_4203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4203_, 0, v_bs_4194_);
                    return v___x_4203_;
                } else {
                    v_v_4204_ = lean_array_uget_borrowed(v_bs_4194_, v_i_4193_);
                    crate::leanh::lean_inc_ref(v___y_4199_);
                    crate::leanh::lean_inc(v_v_4204_);
                    crate::leanh::lean_inc_ref(v_ctx_4191_);
                    crate::leanh::lean_inc_ref(v_containsRecFn_4190_);
                    crate::leanh::lean_inc_ref(v_recFnNames_4189_);
                    crate::leanh::lean_inc_ref(v_params_4188_);
                    crate::leanh::lean_inc_ref(v_positions_4187_);
                    crate::leanh::lean_inc_ref(v_recArgInfos_4186_);
                    v___x_4205_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4186_, v_positions_4187_, v_params_4188_, v_recFnNames_4189_, v_containsRecFn_4190_, v_ctx_4191_, v_v_4204_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
                    if crate::leanh::lean_obj_tag(v___x_4205_) == 0 {
                        v_a_4206_ = crate::leanh::lean_ctor_get(v___x_4205_, 0);
                        crate::leanh::lean_inc(v_a_4206_);
                        crate::leanh::lean_dec_ref_known(v___x_4205_, 1);
                        v___x_4207_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4208_ = lean_array_uset(v_bs_4194_, v_i_4193_, v___x_4207_);
                        v___x_4209_ = 1usize;
                        v___x_4210_ = lean_usize_add(v_i_4193_, v___x_4209_);
                        v___x_4211_ = lean_array_uset(v_bs_x27_4208_, v_i_4193_, v_a_4206_);
                        v_i_4193_ = v___x_4210_;
                        v_bs_4194_ = v___x_4211_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4194_);
                        crate::leanh::lean_dec_ref(v_ctx_4191_);
                        crate::leanh::lean_dec_ref(v_containsRecFn_4190_);
                        crate::leanh::lean_dec_ref(v_recFnNames_4189_);
                        crate::leanh::lean_dec_ref(v_params_4188_);
                        crate::leanh::lean_dec_ref(v_positions_4187_);
                        crate::leanh::lean_dec_ref(v_recArgInfos_4186_);
                        v_a_4213_ = crate::leanh::lean_ctor_get(v___x_4205_, 0);
                        v_isSharedCheck_4220_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4205_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v___x_4215_ = v___x_4205_;
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4213_);
                            crate::leanh::lean_dec(v___x_4205_);
                            v___x_4215_ = crate::leanh::lean_box(0);
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4216_ == 0 {
                    v___x_4218_ = v___x_4215_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4218_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__2(
    mut v_recArgInfos_4221_: *mut crate::leanh::LeanObject,
    mut v_positions_4222_: *mut crate::leanh::LeanObject,
    mut v_params_4223_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4224_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4225_: *mut crate::leanh::LeanObject,
    mut v_ctx_4226_: *mut crate::leanh::LeanObject,
    mut v_e_4227_: *mut crate::leanh::LeanObject,
    mut v_x_4228_: *mut crate::leanh::LeanObject,
    mut v_x_4229_: *mut crate::leanh::LeanObject,
    mut v_x_4230_: *mut crate::leanh::LeanObject,
    mut v___y_4231_: *mut crate::leanh::LeanObject,
    mut v___y_4232_: *mut crate::leanh::LeanObject,
    mut v___y_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
    mut v___y_4235_: *mut crate::leanh::LeanObject,
    mut v___y_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fn_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4244_: usize = 0;
    let mut v___x_4245_: usize = 0;
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4259_: u8 = 0;
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4264_: u8 = 0;
    let mut v_declName_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4228_) == 5 {
                    v_fn_4238_ = crate::leanh::lean_ctor_get(v_x_4228_, 0);
                    crate::leanh::lean_inc_ref(v_fn_4238_);
                    v_arg_4239_ = crate::leanh::lean_ctor_get(v_x_4228_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4239_);
                    crate::leanh::lean_dec_ref_known(v_x_4228_, 2);
                    v___x_4240_ = lean_array_set(v_x_4229_, v_x_4230_, v_arg_4239_);
                    v___x_4241_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4242_ = lean_nat_sub(v_x_4230_, v___x_4241_);
                    crate::leanh::lean_dec(v_x_4230_);
                    v_x_4228_ = v_fn_4238_;
                    v_x_4229_ = v___x_4240_;
                    v_x_4230_ = v___x_4242_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_4230_);
                    v_sz_4244_ = lean_array_size(v_x_4229_);
                    v___x_4245_ = 0usize;
                    crate::leanh::lean_inc_ref(v_ctx_4226_);
                    crate::leanh::lean_inc_ref(v_containsRecFn_4225_);
                    crate::leanh::lean_inc_ref(v_recFnNames_4224_);
                    crate::leanh::lean_inc_ref(v_params_4223_);
                    crate::leanh::lean_inc_ref(v_positions_4222_);
                    crate::leanh::lean_inc_ref(v_recArgInfos_4221_);
                    v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0(v_recArgInfos_4221_, v_positions_4222_, v_params_4223_, v_recFnNames_4224_, v_containsRecFn_4225_, v_ctx_4226_, v_sz_4244_, v___x_4245_, v_x_4229_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
                    if crate::leanh::lean_obj_tag(v___x_4246_) == 0 {
                        v_a_4247_ = crate::leanh::lean_ctor_get(v___x_4246_, 0);
                        crate::leanh::lean_inc(v_a_4247_);
                        crate::leanh::lean_dec_ref_known(v___x_4246_, 1);
                        if crate::leanh::lean_obj_tag(v_x_4228_) == 4 {
                            v_declName_4265_ = crate::leanh::lean_ctor_get(v_x_4228_, 0);
                            v___x_4266_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1(v_recFnNames_4224_, v_declName_4265_);
                            if crate::leanh::lean_obj_tag(v___x_4266_) == 1 {
                                crate::leanh::lean_dec_ref_known(v_x_4228_, 2);
                                crate::leanh::lean_dec_ref(v_containsRecFn_4225_);
                                crate::leanh::lean_dec_ref(v_recFnNames_4224_);
                                crate::leanh::lean_dec_ref(v_params_4223_);
                                v_val_4267_ = crate::leanh::lean_ctor_get(v___x_4266_, 0);
                                crate::leanh::lean_inc(v_val_4267_);
                                crate::leanh::lean_dec_ref_known(v___x_4266_, 1);
                                v___x_4268_ =
                                    l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
                                v___x_4269_ =
                                    lean_array_get(v___x_4268_, v_recArgInfos_4221_, v_val_4267_);
                                crate::leanh::lean_dec_ref(v_recArgInfos_4221_);
                                v___x_4270_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp(v___x_4269_, v_ctx_4226_, v_val_4267_, v_positions_4222_, v_e_4227_, v_a_4247_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
                                crate::leanh::lean_dec(v_a_4247_);
                                crate::leanh::lean_dec_ref(v_positions_4222_);
                                crate::leanh::lean_dec(v_val_4267_);
                                crate::leanh::lean_dec_ref(v_ctx_4226_);
                                crate::leanh::lean_dec(v___x_4269_);
                                return v___x_4270_;
                            } else {
                                crate::leanh::lean_dec(v___x_4266_);
                                crate::leanh::lean_dec_ref(v_e_4227_);
                                v___y_4249_ = v___y_4231_;
                                v___y_4250_ = v___y_4232_;
                                v___y_4251_ = v___y_4233_;
                                v___y_4252_ = v___y_4234_;
                                v___y_4253_ = v___y_4235_;
                                v___y_4254_ = v___y_4236_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_4227_);
                            v___y_4249_ = v___y_4231_;
                            v___y_4250_ = v___y_4232_;
                            v___y_4251_ = v___y_4233_;
                            v___y_4252_ = v___y_4234_;
                            v___y_4253_ = v___y_4235_;
                            v___y_4254_ = v___y_4236_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_4228_);
                        crate::leanh::lean_dec_ref(v_e_4227_);
                        crate::leanh::lean_dec_ref(v_ctx_4226_);
                        crate::leanh::lean_dec_ref(v_containsRecFn_4225_);
                        crate::leanh::lean_dec_ref(v_recFnNames_4224_);
                        crate::leanh::lean_dec_ref(v_params_4223_);
                        crate::leanh::lean_dec_ref(v_positions_4222_);
                        crate::leanh::lean_dec_ref(v_recArgInfos_4221_);
                        v_a_4271_ = crate::leanh::lean_ctor_get(v___x_4246_, 0);
                        v_isSharedCheck_4278_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4246_)) as u8;
                        if v_isSharedCheck_4278_ == 0 {
                            v___x_4273_ = v___x_4246_;
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4271_);
                            crate::leanh::lean_dec(v___x_4246_);
                            v___x_4273_ = crate::leanh::lean_box(0);
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_4253_);
                v___x_4255_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4221_, v_positions_4222_, v_params_4223_, v_recFnNames_4224_, v_containsRecFn_4225_, v_ctx_4226_, v_x_4228_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
                if crate::leanh::lean_obj_tag(v___x_4255_) == 0 {
                    v_a_4256_ = crate::leanh::lean_ctor_get(v___x_4255_, 0);
                    v_isSharedCheck_4264_ = (!crate::leanh::lean_is_exclusive(v___x_4255_)) as u8;
                    if v_isSharedCheck_4264_ == 0 {
                        v___x_4258_ = v___x_4255_;
                        v_isShared_4259_ = v_isSharedCheck_4264_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4256_);
                        crate::leanh::lean_dec(v___x_4255_);
                        v___x_4258_ = crate::leanh::lean_box(0);
                        v_isShared_4259_ = v_isSharedCheck_4264_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4247_);
                    return v___x_4255_;
                }
            }
            2 => {
                v___x_4260_ = l_Lean_mkAppN(v_a_4256_, v_a_4247_);
                crate::leanh::lean_dec(v_a_4247_);
                if v_isShared_4259_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4258_, 0, v___x_4260_);
                    v___x_4262_ = v___x_4258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4263_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
                    v___x_4262_ = v_reuseFailAlloc_4263_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4262_;
            }
            4 => {
                if v_isShared_4274_ == 0 {
                    v___x_4276_ = v___x_4273_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
                    v___x_4276_ = v_reuseFailAlloc_4277_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__0(
    mut v_body_4279_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_4280_: *mut crate::leanh::LeanObject,
    mut v_positions_4281_: *mut crate::leanh::LeanObject,
    mut v_params_4282_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4283_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4284_: *mut crate::leanh::LeanObject,
    mut v_ctx_4285_: *mut crate::leanh::LeanObject,
    mut v_a_4286_: u8,
    mut v_x_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
    mut v___y_4292_: *mut crate::leanh::LeanObject,
    mut v___y_4293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4295_ = lean_expr_instantiate1(v_body_4279_, v_x_4287_);
    crate::leanh::lean_inc_ref(v___y_4292_);
    v___x_4296_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4280_, v_positions_4281_, v_params_4282_, v_recFnNames_4283_, v_containsRecFn_4284_, v_ctx_4285_, v___x_4295_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
    if crate::leanh::lean_obj_tag(v___x_4296_) == 0 {
        let mut v_a_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: u8 = 0;
        let mut v___x_4302_: u8 = 0;
        let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4297_ = crate::leanh::lean_ctor_get(v___x_4296_, 0);
        crate::leanh::lean_inc(v_a_4297_);
        crate::leanh::lean_dec_ref_known(v___x_4296_, 1);
        v___x_4298_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4299_ = lean_mk_empty_array_with_capacity(v___x_4298_);
        v___x_4300_ = lean_array_push(v___x_4299_, v_x_4287_);
        v___x_4301_ = 0;
        v___x_4302_ = 1;
        v___x_4303_ = l_Lean_Meta_mkLambdaFVars(
            v___x_4300_,
            v_a_4297_,
            v___x_4301_,
            v_a_4286_,
            v___x_4301_,
            v_a_4286_,
            v___x_4302_,
            v___y_4290_,
            v___y_4291_,
            v___y_4292_,
            v___y_4293_,
        );
        crate::leanh::lean_dec_ref(v___x_4300_);
        return v___x_4303_;
    } else {
        crate::leanh::lean_dec_ref(v_x_4287_);
        return v___x_4296_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__0___boxed(
    mut v_body_4304_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_4305_: *mut crate::leanh::LeanObject,
    mut v_positions_4306_: *mut crate::leanh::LeanObject,
    mut v_params_4307_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4308_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4309_: *mut crate::leanh::LeanObject,
    mut v_ctx_4310_: *mut crate::leanh::LeanObject,
    mut v_a_4311_: *mut crate::leanh::LeanObject,
    mut v_x_4312_: *mut crate::leanh::LeanObject,
    mut v___y_4313_: *mut crate::leanh::LeanObject,
    mut v___y_4314_: *mut crate::leanh::LeanObject,
    mut v___y_4315_: *mut crate::leanh::LeanObject,
    mut v___y_4316_: *mut crate::leanh::LeanObject,
    mut v___y_4317_: *mut crate::leanh::LeanObject,
    mut v___y_4318_: *mut crate::leanh::LeanObject,
    mut v___y_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_34753__boxed_4320_: u8 = 0;
    let mut v_res_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_34753__boxed_4320_ = (crate::leanh::lean_unbox(v_a_4311_) as u8);
    v_res_4321_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__0(v_body_4304_, v_recArgInfos_4305_, v_positions_4306_, v_params_4307_, v_recFnNames_4308_, v_containsRecFn_4309_, v_ctx_4310_, v_a_34753__boxed_4320_, v_x_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
    crate::leanh::lean_dec(v___y_4318_);
    crate::leanh::lean_dec_ref(v___y_4317_);
    crate::leanh::lean_dec(v___y_4316_);
    crate::leanh::lean_dec_ref(v___y_4315_);
    crate::leanh::lean_dec(v___y_4314_);
    crate::leanh::lean_dec(v___y_4313_);
    crate::leanh::lean_dec_ref(v_body_4304_);
    return v_res_4321_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1(
    mut v_body_4322_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_4323_: *mut crate::leanh::LeanObject,
    mut v_positions_4324_: *mut crate::leanh::LeanObject,
    mut v_params_4325_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4326_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4327_: *mut crate::leanh::LeanObject,
    mut v_ctx_4328_: *mut crate::leanh::LeanObject,
    mut v_a_4329_: u8,
    mut v_x_4330_: *mut crate::leanh::LeanObject,
    mut v___y_4331_: *mut crate::leanh::LeanObject,
    mut v___y_4332_: *mut crate::leanh::LeanObject,
    mut v___y_4333_: *mut crate::leanh::LeanObject,
    mut v___y_4334_: *mut crate::leanh::LeanObject,
    mut v___y_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4338_ = lean_expr_instantiate1(v_body_4322_, v_x_4330_);
    crate::leanh::lean_inc_ref(v___y_4335_);
    v___x_4339_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4323_, v_positions_4324_, v_params_4325_, v_recFnNames_4326_, v_containsRecFn_4327_, v_ctx_4328_, v___x_4338_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
    if crate::leanh::lean_obj_tag(v___x_4339_) == 0 {
        let mut v_a_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4344_: u8 = 0;
        let mut v___x_4345_: u8 = 0;
        let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4340_ = crate::leanh::lean_ctor_get(v___x_4339_, 0);
        crate::leanh::lean_inc(v_a_4340_);
        crate::leanh::lean_dec_ref_known(v___x_4339_, 1);
        v___x_4341_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_4342_ = lean_mk_empty_array_with_capacity(v___x_4341_);
        v___x_4343_ = lean_array_push(v___x_4342_, v_x_4330_);
        v___x_4344_ = 0;
        v___x_4345_ = 1;
        v___x_4346_ = l_Lean_Meta_mkForallFVars(
            v___x_4343_,
            v_a_4340_,
            v___x_4344_,
            v_a_4329_,
            v_a_4329_,
            v___x_4345_,
            v___y_4333_,
            v___y_4334_,
            v___y_4335_,
            v___y_4336_,
        );
        crate::leanh::lean_dec_ref(v___x_4343_);
        return v___x_4346_;
    } else {
        crate::leanh::lean_dec_ref(v_x_4330_);
        return v___x_4339_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1___boxed(
    mut v_body_4347_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_4348_: *mut crate::leanh::LeanObject,
    mut v_positions_4349_: *mut crate::leanh::LeanObject,
    mut v_params_4350_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4351_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4352_: *mut crate::leanh::LeanObject,
    mut v_ctx_4353_: *mut crate::leanh::LeanObject,
    mut v_a_4354_: *mut crate::leanh::LeanObject,
    mut v_x_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
    mut v___y_4357_: *mut crate::leanh::LeanObject,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
    mut v___y_4360_: *mut crate::leanh::LeanObject,
    mut v___y_4361_: *mut crate::leanh::LeanObject,
    mut v___y_4362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_34772__boxed_4363_: u8 = 0;
    let mut v_res_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_34772__boxed_4363_ = (crate::leanh::lean_unbox(v_a_4354_) as u8);
    v_res_4364_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1(v_body_4347_, v_recArgInfos_4348_, v_positions_4349_, v_params_4350_, v_recFnNames_4351_, v_containsRecFn_4352_, v_ctx_4353_, v_a_34772__boxed_4363_, v_x_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
    crate::leanh::lean_dec(v___y_4361_);
    crate::leanh::lean_dec_ref(v___y_4360_);
    crate::leanh::lean_dec(v___y_4359_);
    crate::leanh::lean_dec_ref(v___y_4358_);
    crate::leanh::lean_dec(v___y_4357_);
    crate::leanh::lean_dec(v___y_4356_);
    crate::leanh::lean_dec_ref(v_body_4347_);
    return v_res_4364_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2(
    mut v_body_4365_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_4366_: *mut crate::leanh::LeanObject,
    mut v_positions_4367_: *mut crate::leanh::LeanObject,
    mut v_params_4368_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4369_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4370_: *mut crate::leanh::LeanObject,
    mut v_ctx_4371_: *mut crate::leanh::LeanObject,
    mut v_x_4372_: *mut crate::leanh::LeanObject,
    mut v___y_4373_: *mut crate::leanh::LeanObject,
    mut v___y_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
    mut v___y_4376_: *mut crate::leanh::LeanObject,
    mut v___y_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4380_ = lean_expr_instantiate1(v_body_4365_, v_x_4372_);
    crate::leanh::lean_inc_ref(v___y_4377_);
    v___x_4381_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4366_, v_positions_4367_, v_params_4368_, v_recFnNames_4369_, v_containsRecFn_4370_, v_ctx_4371_, v___x_4380_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
    return v___x_4381_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2___boxed(
    mut v_body_4382_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_4383_: *mut crate::leanh::LeanObject,
    mut v_positions_4384_: *mut crate::leanh::LeanObject,
    mut v_params_4385_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4386_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4387_: *mut crate::leanh::LeanObject,
    mut v_ctx_4388_: *mut crate::leanh::LeanObject,
    mut v_x_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
    mut v___y_4392_: *mut crate::leanh::LeanObject,
    mut v___y_4393_: *mut crate::leanh::LeanObject,
    mut v___y_4394_: *mut crate::leanh::LeanObject,
    mut v___y_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4397_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2(v_body_4382_, v_recArgInfos_4383_, v_positions_4384_, v_params_4385_, v_recFnNames_4386_, v_containsRecFn_4387_, v_ctx_4388_, v_x_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
    crate::leanh::lean_dec(v___y_4395_);
    crate::leanh::lean_dec_ref(v___y_4394_);
    crate::leanh::lean_dec(v___y_4393_);
    crate::leanh::lean_dec_ref(v___y_4392_);
    crate::leanh::lean_dec(v___y_4391_);
    crate::leanh::lean_dec(v___y_4390_);
    crate::leanh::lean_dec_ref(v_x_4389_);
    crate::leanh::lean_dec_ref(v_body_4382_);
    return v_res_4397_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__3___boxed(
    mut v_recArgInfos_4398_: *mut crate::leanh::LeanObject,
    mut v_positions_4399_: *mut crate::leanh::LeanObject,
    mut v_params_4400_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4401_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v_ctx_4405_: *mut crate::leanh::LeanObject,
    mut v_e_4406_: *mut crate::leanh::LeanObject,
    mut v___y_4407_: *mut crate::leanh::LeanObject,
    mut v___y_4408_: *mut crate::leanh::LeanObject,
    mut v___y_4409_: *mut crate::leanh::LeanObject,
    mut v___y_4410_: *mut crate::leanh::LeanObject,
    mut v___y_4411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4412_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__3(v_recArgInfos_4398_, v_positions_4399_, v_params_4400_, v_recFnNames_4401_, v_containsRecFn_4402_, v___y_4403_, v___y_4404_, v_ctx_4405_, v_e_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
    crate::leanh::lean_dec(v___y_4410_);
    crate::leanh::lean_dec_ref(v___y_4409_);
    crate::leanh::lean_dec(v___y_4408_);
    crate::leanh::lean_dec_ref(v___y_4407_);
    crate::leanh::lean_dec(v___y_4404_);
    crate::leanh::lean_dec(v___y_4403_);
    return v_res_4412_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4423_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3;
    v___x_4424_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5;
    v___x_4425_ = l_Lean_Name_append(v___x_4424_, v___x_4423_);
    return v___x_4425_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4427_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7;
    v___x_4428_ = l_Lean_stringToMessageData(v___x_4427_);
    return v___x_4428_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(
    mut v_recArgInfos_4429_: *mut crate::leanh::LeanObject,
    mut v_positions_4430_: *mut crate::leanh::LeanObject,
    mut v_params_4431_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4432_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4433_: *mut crate::leanh::LeanObject,
    mut v_ctx_4434_: *mut crate::leanh::LeanObject,
    mut v_e_4435_: *mut crate::leanh::LeanObject,
    mut v_a_4436_: *mut crate::leanh::LeanObject,
    mut v_a_4437_: *mut crate::leanh::LeanObject,
    mut v_a_4438_: *mut crate::leanh::LeanObject,
    mut v_a_4439_: *mut crate::leanh::LeanObject,
    mut v_a_4440_: *mut crate::leanh::LeanObject,
    mut v_a_4441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: u8 = 0;
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4469_: u8 = 0;
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: u8 = 0;
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4478_: u8 = 0;
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: u8 = 0;
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_4488_: u8 = 0;
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4513_: u8 = 0;
    let mut v_cancelTk_x3f_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4515_: u8 = 0;
    let mut v_inheritedTraceOptions_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4525_: usize = 0;
    let mut v___x_4526_: usize = 0;
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut v_typeName_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4544_: usize = 0;
    let mut v___x_4545_: usize = 0;
    let mut v___x_4546_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4554_: u8 = 0;
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4584_: u8 = 0;
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: u8 = 0;
    let mut v___x_4591_: usize = 0;
    let mut v___x_4592_: usize = 0;
    let mut v___x_4593_: u8 = 0;
    let mut v_options_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4595_: u8 = 0;
    let mut v_inheritedTraceOptions_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut v_a_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4616_: u8 = 0;
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4620_: u8 = 0;
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v___x_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4628_: u8 = 0;
    let mut v_unused_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4633_: u8 = 0;
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4637_: u8 = 0;
    let mut v_isSharedCheck_4638_: u8 = 0;
    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_containsRecFn_4433_);
                crate::leanh::lean_inc(v_a_4441_);
                crate::leanh::lean_inc_ref(v_a_4440_);
                crate::leanh::lean_inc(v_a_4439_);
                crate::leanh::lean_inc_ref(v_a_4438_);
                crate::leanh::lean_inc(v_a_4437_);
                crate::leanh::lean_inc(v_a_4436_);
                crate::leanh::lean_inc_ref(v_e_4435_);
                v___x_4457_ = crate::leanh::lean_apply_8(
                    v_containsRecFn_4433_,
                    v_e_4435_,
                    v_a_4436_,
                    v_a_4437_,
                    v_a_4438_,
                    v_a_4439_,
                    v_a_4440_,
                    v_a_4441_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4638_ = (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4638_ == 0 {
                        v___x_4460_ = v___x_4457_;
                        v_isShared_4461_ = v_isSharedCheck_4638_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4458_);
                        crate::leanh::lean_dec(v___x_4457_);
                        v___x_4460_ = crate::leanh::lean_box(0);
                        v_isShared_4461_ = v_isSharedCheck_4638_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_4440_);
                    crate::leanh::lean_dec_ref(v_e_4435_);
                    crate::leanh::lean_dec_ref(v_ctx_4434_);
                    crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                    crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                    crate::leanh::lean_dec_ref(v_params_4431_);
                    crate::leanh::lean_dec_ref(v_positions_4430_);
                    crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                    v_a_4639_ = crate::leanh::lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4646_ = (!crate::leanh::lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4646_ == 0 {
                        v___x_4641_ = v___x_4457_;
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4639_);
                        crate::leanh::lean_dec(v___x_4457_);
                        v___x_4641_ = crate::leanh::lean_box(0);
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v_dummy_4451_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                v_nargs_4452_ = l_Lean_Expr_getAppNumArgs(v_e_4444_);
                crate::leanh::lean_inc(v_nargs_4452_);
                v___x_4453_ = lean_mk_array(v_nargs_4452_, v_dummy_4451_);
                v___x_4454_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4455_ = lean_nat_sub(v_nargs_4452_, v___x_4454_);
                crate::leanh::lean_dec(v_nargs_4452_);
                crate::leanh::lean_inc_ref(v_e_4444_);
                v___x_4456_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__2(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_e_4444_, v_e_4444_, v___x_4453_, v___x_4455_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
                crate::leanh::lean_dec_ref(v___y_4449_);
                return v___x_4456_;
            }
            2 => {
                v___x_4462_ = (crate::leanh::lean_unbox(v_a_4458_) as u8);
                if v___x_4462_ == 0 {
                    crate::leanh::lean_dec(v_a_4458_);
                    crate::leanh::lean_dec_ref(v_a_4440_);
                    crate::leanh::lean_dec_ref(v_ctx_4434_);
                    crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                    crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                    crate::leanh::lean_dec_ref(v_params_4431_);
                    crate::leanh::lean_dec_ref(v_positions_4430_);
                    crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                    if v_isShared_4461_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4460_, 0, v_e_4435_);
                        v___x_4464_ = v___x_4460_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_e_4435_);
                        v___x_4464_ = v_reuseFailAlloc_4465_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4460_);
                    match crate::leanh::lean_obj_tag(v_e_4435_) {
                        6 => {
                            v_binderName_4466_ = crate::leanh::lean_ctor_get(v_e_4435_, 0);
                            crate::leanh::lean_inc(v_binderName_4466_);
                            v_binderType_4467_ = crate::leanh::lean_ctor_get(v_e_4435_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_4467_);
                            v_body_4468_ = crate::leanh::lean_ctor_get(v_e_4435_, 2);
                            crate::leanh::lean_inc_ref(v_body_4468_);
                            v_binderInfo_4469_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_4435_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_dec_ref_known(v_e_4435_, 3);
                            crate::leanh::lean_inc_ref(v_a_4440_);
                            crate::leanh::lean_inc_ref(v_ctx_4434_);
                            crate::leanh::lean_inc_ref(v_containsRecFn_4433_);
                            crate::leanh::lean_inc_ref(v_recFnNames_4432_);
                            crate::leanh::lean_inc_ref(v_params_4431_);
                            crate::leanh::lean_inc_ref(v_positions_4430_);
                            crate::leanh::lean_inc_ref(v_recArgInfos_4429_);
                            v___x_4470_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_binderType_4467_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if crate::leanh::lean_obj_tag(v___x_4470_) == 0 {
                                v_a_4471_ = crate::leanh::lean_ctor_get(v___x_4470_, 0);
                                crate::leanh::lean_inc(v_a_4471_);
                                crate::leanh::lean_dec_ref_known(v___x_4470_, 1);
                                v___f_4472_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__0___boxed as *mut core::ffi::c_void, 16, 8);
                                crate::leanh::lean_closure_set(v___f_4472_, 0, v_body_4468_);
                                crate::leanh::lean_closure_set(v___f_4472_, 1, v_recArgInfos_4429_);
                                crate::leanh::lean_closure_set(v___f_4472_, 2, v_positions_4430_);
                                crate::leanh::lean_closure_set(v___f_4472_, 3, v_params_4431_);
                                crate::leanh::lean_closure_set(v___f_4472_, 4, v_recFnNames_4432_);
                                crate::leanh::lean_closure_set(
                                    v___f_4472_,
                                    5,
                                    v_containsRecFn_4433_,
                                );
                                crate::leanh::lean_closure_set(v___f_4472_, 6, v_ctx_4434_);
                                crate::leanh::lean_closure_set(v___f_4472_, 7, v_a_4458_);
                                v___x_4473_ = 0;
                                v___x_4474_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_binderName_4466_, v_binderInfo_4469_, v_a_4471_, v___f_4472_, v___x_4473_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                crate::leanh::lean_dec_ref(v_a_4440_);
                                return v___x_4474_;
                            } else {
                                crate::leanh::lean_dec_ref(v_body_4468_);
                                crate::leanh::lean_dec(v_binderName_4466_);
                                crate::leanh::lean_dec(v_a_4458_);
                                crate::leanh::lean_dec_ref(v_a_4440_);
                                crate::leanh::lean_dec_ref(v_ctx_4434_);
                                crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                                crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                                crate::leanh::lean_dec_ref(v_params_4431_);
                                crate::leanh::lean_dec_ref(v_positions_4430_);
                                crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                                return v___x_4470_;
                            }
                        }
                        7 => {
                            v_binderName_4475_ = crate::leanh::lean_ctor_get(v_e_4435_, 0);
                            crate::leanh::lean_inc(v_binderName_4475_);
                            v_binderType_4476_ = crate::leanh::lean_ctor_get(v_e_4435_, 1);
                            crate::leanh::lean_inc_ref(v_binderType_4476_);
                            v_body_4477_ = crate::leanh::lean_ctor_get(v_e_4435_, 2);
                            crate::leanh::lean_inc_ref(v_body_4477_);
                            v_binderInfo_4478_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_4435_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_dec_ref_known(v_e_4435_, 3);
                            crate::leanh::lean_inc_ref(v_a_4440_);
                            crate::leanh::lean_inc_ref(v_ctx_4434_);
                            crate::leanh::lean_inc_ref(v_containsRecFn_4433_);
                            crate::leanh::lean_inc_ref(v_recFnNames_4432_);
                            crate::leanh::lean_inc_ref(v_params_4431_);
                            crate::leanh::lean_inc_ref(v_positions_4430_);
                            crate::leanh::lean_inc_ref(v_recArgInfos_4429_);
                            v___x_4479_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_binderType_4476_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if crate::leanh::lean_obj_tag(v___x_4479_) == 0 {
                                v_a_4480_ = crate::leanh::lean_ctor_get(v___x_4479_, 0);
                                crate::leanh::lean_inc(v_a_4480_);
                                crate::leanh::lean_dec_ref_known(v___x_4479_, 1);
                                v___f_4481_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1___boxed as *mut core::ffi::c_void, 16, 8);
                                crate::leanh::lean_closure_set(v___f_4481_, 0, v_body_4477_);
                                crate::leanh::lean_closure_set(v___f_4481_, 1, v_recArgInfos_4429_);
                                crate::leanh::lean_closure_set(v___f_4481_, 2, v_positions_4430_);
                                crate::leanh::lean_closure_set(v___f_4481_, 3, v_params_4431_);
                                crate::leanh::lean_closure_set(v___f_4481_, 4, v_recFnNames_4432_);
                                crate::leanh::lean_closure_set(
                                    v___f_4481_,
                                    5,
                                    v_containsRecFn_4433_,
                                );
                                crate::leanh::lean_closure_set(v___f_4481_, 6, v_ctx_4434_);
                                crate::leanh::lean_closure_set(v___f_4481_, 7, v_a_4458_);
                                v___x_4482_ = 0;
                                v___x_4483_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_binderName_4475_, v_binderInfo_4478_, v_a_4480_, v___f_4481_, v___x_4482_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                crate::leanh::lean_dec_ref(v_a_4440_);
                                return v___x_4483_;
                            } else {
                                crate::leanh::lean_dec_ref(v_body_4477_);
                                crate::leanh::lean_dec(v_binderName_4475_);
                                crate::leanh::lean_dec(v_a_4458_);
                                crate::leanh::lean_dec_ref(v_a_4440_);
                                crate::leanh::lean_dec_ref(v_ctx_4434_);
                                crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                                crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                                crate::leanh::lean_dec_ref(v_params_4431_);
                                crate::leanh::lean_dec_ref(v_positions_4430_);
                                crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                                return v___x_4479_;
                            }
                        }
                        8 => {
                            v_declName_4484_ = crate::leanh::lean_ctor_get(v_e_4435_, 0);
                            crate::leanh::lean_inc(v_declName_4484_);
                            v_type_4485_ = crate::leanh::lean_ctor_get(v_e_4435_, 1);
                            crate::leanh::lean_inc_ref(v_type_4485_);
                            v_value_4486_ = crate::leanh::lean_ctor_get(v_e_4435_, 2);
                            crate::leanh::lean_inc_ref(v_value_4486_);
                            v_body_4487_ = crate::leanh::lean_ctor_get(v_e_4435_, 3);
                            crate::leanh::lean_inc_ref(v_body_4487_);
                            v_nondep_4488_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_4435_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_dec_ref_known(v_e_4435_, 4);
                            crate::leanh::lean_inc_ref(v_a_4440_);
                            crate::leanh::lean_inc_ref(v_ctx_4434_);
                            crate::leanh::lean_inc_ref(v_containsRecFn_4433_);
                            crate::leanh::lean_inc_ref(v_recFnNames_4432_);
                            crate::leanh::lean_inc_ref(v_params_4431_);
                            crate::leanh::lean_inc_ref(v_positions_4430_);
                            crate::leanh::lean_inc_ref(v_recArgInfos_4429_);
                            v___x_4489_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_type_4485_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if crate::leanh::lean_obj_tag(v___x_4489_) == 0 {
                                v_a_4490_ = crate::leanh::lean_ctor_get(v___x_4489_, 0);
                                crate::leanh::lean_inc(v_a_4490_);
                                crate::leanh::lean_dec_ref_known(v___x_4489_, 1);
                                crate::leanh::lean_inc_ref(v_a_4440_);
                                crate::leanh::lean_inc_ref(v_ctx_4434_);
                                crate::leanh::lean_inc_ref(v_containsRecFn_4433_);
                                crate::leanh::lean_inc_ref(v_recFnNames_4432_);
                                crate::leanh::lean_inc_ref(v_params_4431_);
                                crate::leanh::lean_inc_ref(v_positions_4430_);
                                crate::leanh::lean_inc_ref(v_recArgInfos_4429_);
                                v___x_4491_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_value_4486_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                if crate::leanh::lean_obj_tag(v___x_4491_) == 0 {
                                    v_a_4492_ = crate::leanh::lean_ctor_get(v___x_4491_, 0);
                                    crate::leanh::lean_inc(v_a_4492_);
                                    crate::leanh::lean_dec_ref_known(v___x_4491_, 1);
                                    v___f_4493_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2___boxed as *mut core::ffi::c_void, 15, 7);
                                    crate::leanh::lean_closure_set(v___f_4493_, 0, v_body_4487_);
                                    crate::leanh::lean_closure_set(
                                        v___f_4493_,
                                        1,
                                        v_recArgInfos_4429_,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_4493_,
                                        2,
                                        v_positions_4430_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4493_, 3, v_params_4431_);
                                    crate::leanh::lean_closure_set(
                                        v___f_4493_,
                                        4,
                                        v_recFnNames_4432_,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_4493_,
                                        5,
                                        v_containsRecFn_4433_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_4493_, 6, v_ctx_4434_);
                                    v___x_4494_ = 0;
                                    v___x_4495_ = (crate::leanh::lean_unbox(v_a_4458_) as u8);
                                    crate::leanh::lean_dec(v_a_4458_);
                                    v___x_4496_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4(v_declName_4484_, v_a_4490_, v_a_4492_, v___f_4493_, v_nondep_4488_, v___x_4494_, v___x_4495_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                    crate::leanh::lean_dec_ref(v_a_4440_);
                                    return v___x_4496_;
                                } else {
                                    crate::leanh::lean_dec(v_a_4490_);
                                    crate::leanh::lean_dec_ref(v_body_4487_);
                                    crate::leanh::lean_dec(v_declName_4484_);
                                    crate::leanh::lean_dec(v_a_4458_);
                                    crate::leanh::lean_dec_ref(v_a_4440_);
                                    crate::leanh::lean_dec_ref(v_ctx_4434_);
                                    crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                                    crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                                    crate::leanh::lean_dec_ref(v_params_4431_);
                                    crate::leanh::lean_dec_ref(v_positions_4430_);
                                    crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                                    return v___x_4491_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_body_4487_);
                                crate::leanh::lean_dec_ref(v_value_4486_);
                                crate::leanh::lean_dec(v_declName_4484_);
                                crate::leanh::lean_dec(v_a_4458_);
                                crate::leanh::lean_dec_ref(v_a_4440_);
                                crate::leanh::lean_dec_ref(v_ctx_4434_);
                                crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                                crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                                crate::leanh::lean_dec_ref(v_params_4431_);
                                crate::leanh::lean_dec_ref(v_positions_4430_);
                                crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                                return v___x_4489_;
                            }
                        }
                        10 => {
                            crate::leanh::lean_dec(v_a_4458_);
                            v_data_4497_ = crate::leanh::lean_ctor_get(v_e_4435_, 0);
                            v_expr_4498_ = crate::leanh::lean_ctor_get(v_e_4435_, 1);
                            v___x_4499_ = l_Lean_getRecAppSyntax_x3f(v_e_4435_);
                            if crate::leanh::lean_obj_tag(v___x_4499_) == 1 {
                                crate::leanh::lean_inc_ref(v_expr_4498_);
                                crate::leanh::lean_dec_ref_known(v_e_4435_, 2);
                                v_val_4500_ = crate::leanh::lean_ctor_get(v___x_4499_, 0);
                                crate::leanh::lean_inc(v_val_4500_);
                                crate::leanh::lean_dec_ref_known(v___x_4499_, 1);
                                v_fileName_4501_ = crate::leanh::lean_ctor_get(v_a_4440_, 0);
                                crate::leanh::lean_inc_ref(v_fileName_4501_);
                                v_fileMap_4502_ = crate::leanh::lean_ctor_get(v_a_4440_, 1);
                                crate::leanh::lean_inc_ref(v_fileMap_4502_);
                                v_options_4503_ = crate::leanh::lean_ctor_get(v_a_4440_, 2);
                                crate::leanh::lean_inc_ref(v_options_4503_);
                                v_currRecDepth_4504_ = crate::leanh::lean_ctor_get(v_a_4440_, 3);
                                crate::leanh::lean_inc(v_currRecDepth_4504_);
                                v_maxRecDepth_4505_ = crate::leanh::lean_ctor_get(v_a_4440_, 4);
                                crate::leanh::lean_inc(v_maxRecDepth_4505_);
                                v_ref_4506_ = crate::leanh::lean_ctor_get(v_a_4440_, 5);
                                crate::leanh::lean_inc(v_ref_4506_);
                                v_currNamespace_4507_ = crate::leanh::lean_ctor_get(v_a_4440_, 6);
                                crate::leanh::lean_inc(v_currNamespace_4507_);
                                v_openDecls_4508_ = crate::leanh::lean_ctor_get(v_a_4440_, 7);
                                crate::leanh::lean_inc(v_openDecls_4508_);
                                v_initHeartbeats_4509_ = crate::leanh::lean_ctor_get(v_a_4440_, 8);
                                crate::leanh::lean_inc(v_initHeartbeats_4509_);
                                v_maxHeartbeats_4510_ = crate::leanh::lean_ctor_get(v_a_4440_, 9);
                                crate::leanh::lean_inc(v_maxHeartbeats_4510_);
                                v_quotContext_4511_ = crate::leanh::lean_ctor_get(v_a_4440_, 10);
                                crate::leanh::lean_inc(v_quotContext_4511_);
                                v_currMacroScope_4512_ = crate::leanh::lean_ctor_get(v_a_4440_, 11);
                                crate::leanh::lean_inc(v_currMacroScope_4512_);
                                v_diag_4513_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_4440_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14)
                                        as u32,
                                );
                                v_cancelTk_x3f_4514_ = crate::leanh::lean_ctor_get(v_a_4440_, 12);
                                crate::leanh::lean_inc(v_cancelTk_x3f_4514_);
                                v_suppressElabErrors_4515_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_4440_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1)
                                        as u32,
                                );
                                v_inheritedTraceOptions_4516_ =
                                    crate::leanh::lean_ctor_get(v_a_4440_, 13);
                                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4516_);
                                crate::leanh::lean_dec_ref(v_a_4440_);
                                v_ref_4517_ = l_Lean_replaceRef(v_val_4500_, v_ref_4506_);
                                crate::leanh::lean_dec(v_ref_4506_);
                                crate::leanh::lean_dec(v_val_4500_);
                                v___x_4518_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                                crate::leanh::lean_ctor_set(v___x_4518_, 0, v_fileName_4501_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 1, v_fileMap_4502_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 2, v_options_4503_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 3, v_currRecDepth_4504_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 4, v_maxRecDepth_4505_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 5, v_ref_4517_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 6, v_currNamespace_4507_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 7, v_openDecls_4508_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 8, v_initHeartbeats_4509_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 9, v_maxHeartbeats_4510_);
                                crate::leanh::lean_ctor_set(v___x_4518_, 10, v_quotContext_4511_);
                                crate::leanh::lean_ctor_set(
                                    v___x_4518_,
                                    11,
                                    v_currMacroScope_4512_,
                                );
                                crate::leanh::lean_ctor_set(v___x_4518_, 12, v_cancelTk_x3f_4514_);
                                crate::leanh::lean_ctor_set(
                                    v___x_4518_,
                                    13,
                                    v_inheritedTraceOptions_4516_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_4518_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14)
                                        as u32,
                                    v_diag_4513_,
                                );
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_4518_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1)
                                        as u32,
                                    v_suppressElabErrors_4515_,
                                );
                                v_e_4435_ = v_expr_4498_;
                                v_a_4440_ = v___x_4518_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4499_);
                                crate::leanh::lean_inc_ref(v_expr_4498_);
                                v___x_4520_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_expr_4498_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                if crate::leanh::lean_obj_tag(v___x_4520_) == 0 {
                                    v_a_4521_ = crate::leanh::lean_ctor_get(v___x_4520_, 0);
                                    v_isSharedCheck_4535_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4520_)) as u8;
                                    if v_isSharedCheck_4535_ == 0 {
                                        v___x_4523_ = v___x_4520_;
                                        v_isShared_4524_ = v_isSharedCheck_4535_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4521_);
                                        crate::leanh::lean_dec(v___x_4520_);
                                        v___x_4523_ = crate::leanh::lean_box(0);
                                        v_isShared_4524_ = v_isSharedCheck_4535_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_e_4435_, 2);
                                    return v___x_4520_;
                                }
                            }
                        }
                        11 => {
                            crate::leanh::lean_dec(v_a_4458_);
                            v_typeName_4536_ = crate::leanh::lean_ctor_get(v_e_4435_, 0);
                            v_idx_4537_ = crate::leanh::lean_ctor_get(v_e_4435_, 1);
                            v_struct_4538_ = crate::leanh::lean_ctor_get(v_e_4435_, 2);
                            crate::leanh::lean_inc_ref(v_struct_4538_);
                            v___x_4539_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_struct_4538_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if crate::leanh::lean_obj_tag(v___x_4539_) == 0 {
                                v_a_4540_ = crate::leanh::lean_ctor_get(v___x_4539_, 0);
                                v_isSharedCheck_4554_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4539_)) as u8;
                                if v_isSharedCheck_4554_ == 0 {
                                    v___x_4542_ = v___x_4539_;
                                    v_isShared_4543_ = v_isSharedCheck_4554_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4540_);
                                    crate::leanh::lean_dec(v___x_4539_);
                                    v___x_4542_ = crate::leanh::lean_box(0);
                                    v_isShared_4543_ = v_isSharedCheck_4554_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_4435_, 3);
                                return v___x_4539_;
                            }
                        }
                        5 => {
                            crate::leanh::lean_dec(v_a_4458_);
                            v___x_4555_ = 0;
                            crate::leanh::lean_inc_ref(v_e_4435_);
                            v___x_4556_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5(v_e_4435_, v___x_4555_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if crate::leanh::lean_obj_tag(v___x_4556_) == 0 {
                                v_a_4557_ = crate::leanh::lean_ctor_get(v___x_4556_, 0);
                                crate::leanh::lean_inc(v_a_4557_);
                                crate::leanh::lean_dec_ref_known(v___x_4556_, 1);
                                if crate::leanh::lean_obj_tag(v_a_4557_) == 1 {
                                    v_val_4558_ = crate::leanh::lean_ctor_get(v_a_4557_, 0);
                                    crate::leanh::lean_inc(v_val_4558_);
                                    crate::leanh::lean_dec_ref_known(v_a_4557_, 1);
                                    v___x_4559_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_4589_ = lean_array_get_size(v_recArgInfos_4429_);
                                    v___x_4590_ = lean_nat_dec_lt(v___x_4559_, v___x_4589_);
                                    if v___x_4590_ == 0 {
                                        crate::leanh::lean_dec(v_val_4558_);
                                        v_e_4444_ = v_e_4435_;
                                        v___y_4445_ = v_a_4436_;
                                        v___y_4446_ = v_a_4437_;
                                        v___y_4447_ = v_a_4438_;
                                        v___y_4448_ = v_a_4439_;
                                        v___y_4449_ = v_a_4440_;
                                        v___y_4450_ = v_a_4441_;
                                        state = 1;
                                        continue;
                                    } else {
                                        if v___x_4590_ == 0 {
                                            crate::leanh::lean_dec(v_val_4558_);
                                            v_e_4444_ = v_e_4435_;
                                            v___y_4445_ = v_a_4436_;
                                            v___y_4446_ = v_a_4437_;
                                            v___y_4447_ = v_a_4438_;
                                            v___y_4448_ = v_a_4439_;
                                            v___y_4449_ = v_a_4440_;
                                            v___y_4450_ = v_a_4441_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_4591_ = 0usize;
                                            v___x_4592_ = lean_usize_of_nat(v___x_4589_);
                                            v___x_4593_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__6(v_e_4435_, v_recArgInfos_4429_, v___x_4591_, v___x_4592_);
                                            if v___x_4593_ == 0 {
                                                crate::leanh::lean_dec(v_val_4558_);
                                                v_e_4444_ = v_e_4435_;
                                                v___y_4445_ = v_a_4436_;
                                                v___y_4446_ = v_a_4437_;
                                                v___y_4447_ = v_a_4438_;
                                                v___y_4448_ = v_a_4439_;
                                                v___y_4449_ = v_a_4440_;
                                                v___y_4450_ = v_a_4441_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v_options_4594_ =
                                                    crate::leanh::lean_ctor_get(v_a_4440_, 2);
                                                v_hasTrace_4595_ =
                                                    crate::leanh::lean_ctor_get_uint8(
                                                        v_options_4594_,
                                                        (core::mem::size_of::<
                                                            *mut crate::leanh::LeanObject,
                                                        >(
                                                        ) * 1)
                                                            as u32,
                                                    );
                                                if v_hasTrace_4595_ == 0 {
                                                    v___y_4561_ = v_a_4436_;
                                                    v___y_4562_ = v_a_4437_;
                                                    v___y_4563_ = v_a_4438_;
                                                    v___y_4564_ = v_a_4439_;
                                                    v___y_4565_ = v_a_4440_;
                                                    v___y_4566_ = v_a_4441_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    v_inheritedTraceOptions_4596_ =
                                                        crate::leanh::lean_ctor_get(v_a_4440_, 13);
                                                    v___x_4597_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3;
                                                    v___x_4598_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6);
                                                    v___x_4599_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4596_, v_options_4594_, v___x_4598_);
                                                    if v___x_4599_ == 0 {
                                                        v___y_4561_ = v_a_4436_;
                                                        v___y_4562_ = v_a_4437_;
                                                        v___y_4563_ = v_a_4438_;
                                                        v___y_4564_ = v_a_4439_;
                                                        v___y_4565_ = v_a_4440_;
                                                        v___y_4566_ = v_a_4441_;
                                                        state = 10;
                                                        continue;
                                                    } else {
                                                        v___x_4600_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8);
                                                        crate::leanh::lean_inc(v_val_4558_);
                                                        v___x_4601_ = l_Lean_Meta_MatcherApp_toExpr(
                                                            v_val_4558_,
                                                        );
                                                        v___x_4602_ =
                                                            l_Lean_MessageData_ofExpr(v___x_4601_);
                                                        v___x_4603_ = crate::leanh::lean_alloc_ctor(
                                                            7,
                                                            2,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_4603_,
                                                            0,
                                                            v___x_4600_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_4603_,
                                                            1,
                                                            v___x_4602_,
                                                        );
                                                        v___x_4604_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(v___x_4597_, v___x_4603_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                                        if crate::leanh::lean_obj_tag(v___x_4604_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_4604_,
                                                                1,
                                                            );
                                                            v___y_4561_ = v_a_4436_;
                                                            v___y_4562_ = v_a_4437_;
                                                            v___y_4563_ = v_a_4438_;
                                                            v___y_4564_ = v_a_4439_;
                                                            v___y_4565_ = v_a_4440_;
                                                            v___y_4566_ = v_a_4441_;
                                                            state = 10;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_dec(v_val_4558_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v_e_4435_, 2,
                                                            );
                                                            crate::leanh::lean_dec_ref(v_a_4440_);
                                                            crate::leanh::lean_dec_ref(v_ctx_4434_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_containsRecFn_4433_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_recFnNames_4432_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_params_4431_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_positions_4430_,
                                                            );
                                                            crate::leanh::lean_dec_ref(
                                                                v_recArgInfos_4429_,
                                                            );
                                                            v_a_4605_ = crate::leanh::lean_ctor_get(
                                                                v___x_4604_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4612_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_4604_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4612_ == 0 {
                                                                v___x_4607_ = v___x_4604_;
                                                                v_isShared_4608_ =
                                                                    v_isSharedCheck_4612_;
                                                                state = 13;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_4605_);
                                                                crate::leanh::lean_dec(v___x_4604_);
                                                                v___x_4607_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_4608_ =
                                                                    v_isSharedCheck_4612_;
                                                                state = 13;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4557_);
                                    v_e_4444_ = v_e_4435_;
                                    v___y_4445_ = v_a_4436_;
                                    v___y_4446_ = v_a_4437_;
                                    v___y_4447_ = v_a_4438_;
                                    v___y_4448_ = v_a_4439_;
                                    v___y_4449_ = v_a_4440_;
                                    v___y_4450_ = v_a_4441_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_4435_, 2);
                                crate::leanh::lean_dec_ref(v_a_4440_);
                                crate::leanh::lean_dec_ref(v_ctx_4434_);
                                crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                                crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                                crate::leanh::lean_dec_ref(v_params_4431_);
                                crate::leanh::lean_dec_ref(v_positions_4430_);
                                crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                                v_a_4613_ = crate::leanh::lean_ctor_get(v___x_4556_, 0);
                                v_isSharedCheck_4620_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4556_)) as u8;
                                if v_isSharedCheck_4620_ == 0 {
                                    v___x_4615_ = v___x_4556_;
                                    v_isShared_4616_ = v_isSharedCheck_4620_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4613_);
                                    crate::leanh::lean_dec(v___x_4556_);
                                    v___x_4615_ = crate::leanh::lean_box(0);
                                    v_isShared_4616_ = v_isSharedCheck_4620_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_a_4458_);
                            crate::leanh::lean_dec_ref(v_ctx_4434_);
                            crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                            crate::leanh::lean_dec_ref(v_params_4431_);
                            crate::leanh::lean_dec_ref(v_positions_4430_);
                            crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                            crate::leanh::lean_inc_ref(v_e_4435_);
                            v___x_4621_ = l_Lean_Elab_ensureNoRecFn(
                                v_recFnNames_4432_,
                                v_e_4435_,
                                v_a_4438_,
                                v_a_4439_,
                                v_a_4440_,
                                v_a_4441_,
                            );
                            crate::leanh::lean_dec_ref(v_a_4440_);
                            if crate::leanh::lean_obj_tag(v___x_4621_) == 0 {
                                v_isSharedCheck_4628_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4621_)) as u8;
                                if v_isSharedCheck_4628_ == 0 {
                                    v_unused_4629_ = crate::leanh::lean_ctor_get(v___x_4621_, 0);
                                    crate::leanh::lean_dec(v_unused_4629_);
                                    v___x_4623_ = v___x_4621_;
                                    v_isShared_4624_ = v_isSharedCheck_4628_;
                                    state = 17;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4621_);
                                    v___x_4623_ = crate::leanh::lean_box(0);
                                    v_isShared_4624_ = v_isSharedCheck_4628_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_4435_);
                                v_a_4630_ = crate::leanh::lean_ctor_get(v___x_4621_, 0);
                                v_isSharedCheck_4637_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4621_)) as u8;
                                if v_isSharedCheck_4637_ == 0 {
                                    v___x_4632_ = v___x_4621_;
                                    v_isShared_4633_ = v_isSharedCheck_4637_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4630_);
                                    crate::leanh::lean_dec(v___x_4621_);
                                    v___x_4632_ = crate::leanh::lean_box(0);
                                    v_isShared_4633_ = v_isSharedCheck_4637_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                return v___x_4464_;
            }
            4 => {
                v___x_4525_ = lean_ptr_addr(v_expr_4498_);
                v___x_4526_ = lean_ptr_addr(v_a_4521_);
                v___x_4527_ = lean_usize_dec_eq(v___x_4525_, v___x_4526_);
                if v___x_4527_ == 0 {
                    crate::leanh::lean_inc(v_data_4497_);
                    crate::leanh::lean_dec_ref_known(v_e_4435_, 2);
                    v___x_4528_ = l_Lean_Expr_mdata___override(v_data_4497_, v_a_4521_);
                    if v_isShared_4524_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4523_, 0, v___x_4528_);
                        v___x_4530_ = v___x_4523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4531_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
                        v___x_4530_ = v_reuseFailAlloc_4531_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4521_);
                    if v_isShared_4524_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4523_, 0, v_e_4435_);
                        v___x_4533_ = v___x_4523_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_e_4435_);
                        v___x_4533_ = v_reuseFailAlloc_4534_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4530_;
            }
            6 => {
                return v___x_4533_;
            }
            7 => {
                v___x_4544_ = lean_ptr_addr(v_struct_4538_);
                v___x_4545_ = lean_ptr_addr(v_a_4540_);
                v___x_4546_ = lean_usize_dec_eq(v___x_4544_, v___x_4545_);
                if v___x_4546_ == 0 {
                    crate::leanh::lean_inc(v_idx_4537_);
                    crate::leanh::lean_inc(v_typeName_4536_);
                    crate::leanh::lean_dec_ref_known(v_e_4435_, 3);
                    v___x_4547_ =
                        l_Lean_Expr_proj___override(v_typeName_4536_, v_idx_4537_, v_a_4540_);
                    if v_isShared_4543_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4542_, 0, v___x_4547_);
                        v___x_4549_ = v___x_4542_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
                        v___x_4549_ = v_reuseFailAlloc_4550_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4540_);
                    if v_isShared_4543_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4542_, 0, v_e_4435_);
                        v___x_4552_ = v___x_4542_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4553_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_e_4435_);
                        v___x_4552_ = v_reuseFailAlloc_4553_;
                        state = 9;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_4549_;
            }
            9 => {
                return v___x_4552_;
            }
            10 => {
                v___x_4567_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
                v___x_4568_ =
                    lean_array_get_borrowed(v___x_4567_, v_recArgInfos_4429_, v___x_4559_);
                v_indGroupInst_4569_ = crate::leanh::lean_ctor_get(v___x_4568_, 4);
                v_params_4570_ = crate::leanh::lean_ctor_get(v_indGroupInst_4569_, 2);
                crate::leanh::lean_inc(v___y_4562_);
                crate::leanh::lean_inc(v___y_4561_);
                crate::leanh::lean_inc_ref(v_containsRecFn_4433_);
                crate::leanh::lean_inc_ref(v_recFnNames_4432_);
                crate::leanh::lean_inc_ref_n(v_params_4431_, 2);
                crate::leanh::lean_inc_ref(v_positions_4430_);
                crate::leanh::lean_inc_ref(v_recArgInfos_4429_);
                v___f_4571_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__3___boxed as *mut core::ffi::c_void, 14, 7);
                crate::leanh::lean_closure_set(v___f_4571_, 0, v_recArgInfos_4429_);
                crate::leanh::lean_closure_set(v___f_4571_, 1, v_positions_4430_);
                crate::leanh::lean_closure_set(v___f_4571_, 2, v_params_4431_);
                crate::leanh::lean_closure_set(v___f_4571_, 3, v_recFnNames_4432_);
                crate::leanh::lean_closure_set(v___f_4571_, 4, v_containsRecFn_4433_);
                crate::leanh::lean_closure_set(v___f_4571_, 5, v___y_4561_);
                crate::leanh::lean_closure_set(v___f_4571_, 6, v___y_4562_);
                v___x_4572_ = lean_array_get_size(v_params_4570_);
                crate::leanh::lean_inc_ref(v_ctx_4434_);
                v___x_4573_ = l_Lean_Meta_IndPredBelow_mkBelowMatcher(
                    v_val_4558_,
                    v_params_4431_,
                    v___x_4572_,
                    v_ctx_4434_,
                    v___f_4571_,
                    v___y_4563_,
                    v___y_4564_,
                    v___y_4565_,
                    v___y_4566_,
                );
                if crate::leanh::lean_obj_tag(v___x_4573_) == 0 {
                    v_a_4574_ = crate::leanh::lean_ctor_get(v___x_4573_, 0);
                    crate::leanh::lean_inc(v_a_4574_);
                    crate::leanh::lean_dec_ref_known(v___x_4573_, 1);
                    if crate::leanh::lean_obj_tag(v_a_4574_) == 1 {
                        crate::leanh::lean_dec_ref_known(v_e_4435_, 2);
                        v_val_4575_ = crate::leanh::lean_ctor_get(v_a_4574_, 0);
                        crate::leanh::lean_inc(v_val_4575_);
                        crate::leanh::lean_dec_ref_known(v_a_4574_, 1);
                        v_fst_4576_ = crate::leanh::lean_ctor_get(v_val_4575_, 0);
                        crate::leanh::lean_inc(v_fst_4576_);
                        v_snd_4577_ = crate::leanh::lean_ctor_get(v_val_4575_, 1);
                        crate::leanh::lean_inc(v_snd_4577_);
                        crate::leanh::lean_dec(v_val_4575_);
                        v___x_4578_ = lean_st_ref_take(v___y_4562_);
                        v___x_4579_ = lean_array_push(v___x_4578_, v_snd_4577_);
                        v___x_4580_ = lean_st_ref_set(v___y_4562_, v___x_4579_);
                        v_e_4444_ = v_fst_4576_;
                        v___y_4445_ = v___y_4561_;
                        v___y_4446_ = v___y_4562_;
                        v___y_4447_ = v___y_4563_;
                        v___y_4448_ = v___y_4564_;
                        v___y_4449_ = v___y_4565_;
                        v___y_4450_ = v___y_4566_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_4574_);
                        v_e_4444_ = v_e_4435_;
                        v___y_4445_ = v___y_4561_;
                        v___y_4446_ = v___y_4562_;
                        v___y_4447_ = v___y_4563_;
                        v___y_4448_ = v___y_4564_;
                        v___y_4449_ = v___y_4565_;
                        v___y_4450_ = v___y_4566_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4565_);
                    crate::leanh::lean_dec_ref_known(v_e_4435_, 2);
                    crate::leanh::lean_dec_ref(v_ctx_4434_);
                    crate::leanh::lean_dec_ref(v_containsRecFn_4433_);
                    crate::leanh::lean_dec_ref(v_recFnNames_4432_);
                    crate::leanh::lean_dec_ref(v_params_4431_);
                    crate::leanh::lean_dec_ref(v_positions_4430_);
                    crate::leanh::lean_dec_ref(v_recArgInfos_4429_);
                    v_a_4581_ = crate::leanh::lean_ctor_get(v___x_4573_, 0);
                    v_isSharedCheck_4588_ = (!crate::leanh::lean_is_exclusive(v___x_4573_)) as u8;
                    if v_isSharedCheck_4588_ == 0 {
                        v___x_4583_ = v___x_4573_;
                        v_isShared_4584_ = v_isSharedCheck_4588_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4581_);
                        crate::leanh::lean_dec(v___x_4573_);
                        v___x_4583_ = crate::leanh::lean_box(0);
                        v_isShared_4584_ = v_isSharedCheck_4588_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_4584_ == 0 {
                    v___x_4586_ = v___x_4583_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
                    v___x_4586_ = v_reuseFailAlloc_4587_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4586_;
            }
            13 => {
                if v_isShared_4608_ == 0 {
                    v___x_4610_ = v___x_4607_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
                    v___x_4610_ = v_reuseFailAlloc_4611_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4610_;
            }
            15 => {
                if v_isShared_4616_ == 0 {
                    v___x_4618_ = v___x_4615_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
                    v___x_4618_ = v_reuseFailAlloc_4619_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4618_;
            }
            17 => {
                if v_isShared_4624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4623_, 0, v_e_4435_);
                    v___x_4626_ = v___x_4623_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4627_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_e_4435_);
                    v___x_4626_ = v_reuseFailAlloc_4627_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4626_;
            }
            19 => {
                if v_isShared_4633_ == 0 {
                    v___x_4635_ = v___x_4632_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4636_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
                    v___x_4635_ = v_reuseFailAlloc_4636_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4635_;
            }
            21 => {
                if v_isShared_4642_ == 0 {
                    v___x_4644_ = v___x_4641_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
                    v___x_4644_ = v_reuseFailAlloc_4645_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4644_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__3(
    mut v_recArgInfos_4647_: *mut crate::leanh::LeanObject,
    mut v_positions_4648_: *mut crate::leanh::LeanObject,
    mut v_params_4649_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4650_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
    mut v_ctx_4654_: *mut crate::leanh::LeanObject,
    mut v_e_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v___y_4658_);
    v___x_4661_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4647_, v_positions_4648_, v_params_4649_, v_recFnNames_4650_, v_containsRecFn_4651_, v_ctx_4654_, v_e_4655_, v___y_4652_, v___y_4653_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
    return v___x_4661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0___boxed(
    mut v_recArgInfos_4662_: *mut crate::leanh::LeanObject,
    mut v_positions_4663_: *mut crate::leanh::LeanObject,
    mut v_params_4664_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4665_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4666_: *mut crate::leanh::LeanObject,
    mut v_ctx_4667_: *mut crate::leanh::LeanObject,
    mut v_sz_4668_: *mut crate::leanh::LeanObject,
    mut v_i_4669_: *mut crate::leanh::LeanObject,
    mut v_bs_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
    mut v___y_4672_: *mut crate::leanh::LeanObject,
    mut v___y_4673_: *mut crate::leanh::LeanObject,
    mut v___y_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
    mut v___y_4677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4678_: usize = 0;
    let mut v_i_boxed_4679_: usize = 0;
    let mut v_res_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4678_ = crate::leanh::lean_unbox_usize(v_sz_4668_);
    crate::leanh::lean_dec(v_sz_4668_);
    v_i_boxed_4679_ = crate::leanh::lean_unbox_usize(v_i_4669_);
    crate::leanh::lean_dec(v_i_4669_);
    v_res_4680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0(v_recArgInfos_4662_, v_positions_4663_, v_params_4664_, v_recFnNames_4665_, v_containsRecFn_4666_, v_ctx_4667_, v_sz_boxed_4678_, v_i_boxed_4679_, v_bs_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
    crate::leanh::lean_dec(v___y_4676_);
    crate::leanh::lean_dec_ref(v___y_4675_);
    crate::leanh::lean_dec(v___y_4674_);
    crate::leanh::lean_dec_ref(v___y_4673_);
    crate::leanh::lean_dec(v___y_4672_);
    crate::leanh::lean_dec(v___y_4671_);
    return v_res_4680_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_recArgInfos_4681_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_positions_4682_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_params_4683_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_recFnNames_4684_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_containsRecFn_4685_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_ctx_4686_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_e_4687_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_x_4688_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_x_4689_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_x_4690_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4691_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4692_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4693_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4694_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4695_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4696_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4697_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4698_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__2(v_recArgInfos_4681_, v_positions_4682_, v_params_4683_, v_recFnNames_4684_, v_containsRecFn_4685_, v_ctx_4686_, v_e_4687_, v_x_4688_, v_x_4689_, v_x_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
    crate::leanh::lean_dec(v___y_4696_);
    crate::leanh::lean_dec_ref(v___y_4695_);
    crate::leanh::lean_dec(v___y_4694_);
    crate::leanh::lean_dec_ref(v___y_4693_);
    crate::leanh::lean_dec(v___y_4692_);
    crate::leanh::lean_dec(v___y_4691_);
    return v_res_4698_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___boxed(
    mut v_recArgInfos_4699_: *mut crate::leanh::LeanObject,
    mut v_positions_4700_: *mut crate::leanh::LeanObject,
    mut v_params_4701_: *mut crate::leanh::LeanObject,
    mut v_recFnNames_4702_: *mut crate::leanh::LeanObject,
    mut v_containsRecFn_4703_: *mut crate::leanh::LeanObject,
    mut v_ctx_4704_: *mut crate::leanh::LeanObject,
    mut v_e_4705_: *mut crate::leanh::LeanObject,
    mut v_a_4706_: *mut crate::leanh::LeanObject,
    mut v_a_4707_: *mut crate::leanh::LeanObject,
    mut v_a_4708_: *mut crate::leanh::LeanObject,
    mut v_a_4709_: *mut crate::leanh::LeanObject,
    mut v_a_4710_: *mut crate::leanh::LeanObject,
    mut v_a_4711_: *mut crate::leanh::LeanObject,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4713_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4699_, v_positions_4700_, v_params_4701_, v_recFnNames_4702_, v_containsRecFn_4703_, v_ctx_4704_, v_e_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
    crate::leanh::lean_dec(v_a_4711_);
    crate::leanh::lean_dec(v_a_4709_);
    crate::leanh::lean_dec_ref(v_a_4708_);
    crate::leanh::lean_dec(v_a_4707_);
    crate::leanh::lean_dec(v_a_4706_);
    return v_res_4713_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5(
    mut v_00_u03b1_4714_: *mut crate::leanh::LeanObject,
    mut v_name_4715_: *mut crate::leanh::LeanObject,
    mut v_type_4716_: *mut crate::leanh::LeanObject,
    mut v_val_4717_: *mut crate::leanh::LeanObject,
    mut v_k_4718_: *mut crate::leanh::LeanObject,
    mut v_nondep_4719_: u8,
    mut v_kind_4720_: u8,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
    mut v___y_4722_: *mut crate::leanh::LeanObject,
    mut v___y_4723_: *mut crate::leanh::LeanObject,
    mut v___y_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4728_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(v_name_4715_, v_type_4716_, v_val_4717_, v_k_4718_, v_nondep_4719_, v_kind_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
    return v___x_4728_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___boxed(
    mut v_00_u03b1_4729_: *mut crate::leanh::LeanObject,
    mut v_name_4730_: *mut crate::leanh::LeanObject,
    mut v_type_4731_: *mut crate::leanh::LeanObject,
    mut v_val_4732_: *mut crate::leanh::LeanObject,
    mut v_k_4733_: *mut crate::leanh::LeanObject,
    mut v_nondep_4734_: *mut crate::leanh::LeanObject,
    mut v_kind_4735_: *mut crate::leanh::LeanObject,
    mut v___y_4736_: *mut crate::leanh::LeanObject,
    mut v___y_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_4743_: u8 = 0;
    let mut v_kind_boxed_4744_: u8 = 0;
    let mut v_res_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4743_ = (crate::leanh::lean_unbox(v_nondep_4734_) as u8);
    v_kind_boxed_4744_ = (crate::leanh::lean_unbox(v_kind_4735_) as u8);
    v_res_4745_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5(v_00_u03b1_4729_, v_name_4730_, v_type_4731_, v_val_4732_, v_k_4733_, v_nondep_boxed_4743_, v_kind_boxed_4744_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
    crate::leanh::lean_dec(v___y_4741_);
    crate::leanh::lean_dec_ref(v___y_4740_);
    crate::leanh::lean_dec(v___y_4739_);
    crate::leanh::lean_dec_ref(v___y_4738_);
    crate::leanh::lean_dec(v___y_4737_);
    crate::leanh::lean_dec(v___y_4736_);
    return v_res_4745_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9(
    mut v_declName_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
    mut v___y_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
    mut v___y_4752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4754_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(v_declName_4746_, v___y_4752_);
    return v___x_4754_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___boxed(
    mut v_declName_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9(v_declName_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
    crate::leanh::lean_dec(v___y_4761_);
    crate::leanh::lean_dec_ref(v___y_4760_);
    crate::leanh::lean_dec(v___y_4759_);
    crate::leanh::lean_dec_ref(v___y_4758_);
    crate::leanh::lean_dec(v___y_4757_);
    crate::leanh::lean_dec(v___y_4756_);
    return v_res_4763_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7(
    mut v_cls_4764_: *mut crate::leanh::LeanObject,
    mut v_msg_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
    mut v___y_4767_: *mut crate::leanh::LeanObject,
    mut v___y_4768_: *mut crate::leanh::LeanObject,
    mut v___y_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4773_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(v_cls_4764_, v_msg_4765_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
    return v___x_4773_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___boxed(
    mut v_cls_4774_: *mut crate::leanh::LeanObject,
    mut v_msg_4775_: *mut crate::leanh::LeanObject,
    mut v___y_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
    mut v___y_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7(v_cls_4774_, v_msg_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
    crate::leanh::lean_dec(v___y_4781_);
    crate::leanh::lean_dec_ref(v___y_4780_);
    crate::leanh::lean_dec(v___y_4779_);
    crate::leanh::lean_dec_ref(v___y_4778_);
    crate::leanh::lean_dec(v___y_4777_);
    crate::leanh::lean_dec(v___y_4776_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9(
    mut v_00_u03b1_4784_: *mut crate::leanh::LeanObject,
    mut v_constName_4785_: *mut crate::leanh::LeanObject,
    mut v___y_4786_: *mut crate::leanh::LeanObject,
    mut v___y_4787_: *mut crate::leanh::LeanObject,
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v___y_4789_: *mut crate::leanh::LeanObject,
    mut v___y_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4793_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(v_constName_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
    return v___x_4793_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_4794_: *mut crate::leanh::LeanObject,
    mut v_constName_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
    mut v___y_4802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4803_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9(v_00_u03b1_4794_, v_constName_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
    crate::leanh::lean_dec(v___y_4801_);
    crate::leanh::lean_dec_ref(v___y_4800_);
    crate::leanh::lean_dec(v___y_4799_);
    crate::leanh::lean_dec_ref(v___y_4798_);
    crate::leanh::lean_dec(v___y_4797_);
    crate::leanh::lean_dec(v___y_4796_);
    return v_res_4803_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14(
    mut v_00_u03b1_4804_: *mut crate::leanh::LeanObject,
    mut v_ref_4805_: *mut crate::leanh::LeanObject,
    mut v_constName_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4814_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(v_ref_4805_, v_constName_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
    return v___x_4814_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___boxed(
    mut v_00_u03b1_4815_: *mut crate::leanh::LeanObject,
    mut v_ref_4816_: *mut crate::leanh::LeanObject,
    mut v_constName_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
    mut v___y_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4825_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14(v_00_u03b1_4815_, v_ref_4816_, v_constName_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
    crate::leanh::lean_dec(v___y_4823_);
    crate::leanh::lean_dec_ref(v___y_4822_);
    crate::leanh::lean_dec(v___y_4821_);
    crate::leanh::lean_dec_ref(v___y_4820_);
    crate::leanh::lean_dec(v___y_4819_);
    crate::leanh::lean_dec(v___y_4818_);
    crate::leanh::lean_dec(v_ref_4816_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16(
    mut v_00_u03b1_4826_: *mut crate::leanh::LeanObject,
    mut v_ref_4827_: *mut crate::leanh::LeanObject,
    mut v_msg_4828_: *mut crate::leanh::LeanObject,
    mut v_declHint_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
    mut v___y_4831_: *mut crate::leanh::LeanObject,
    mut v___y_4832_: *mut crate::leanh::LeanObject,
    mut v___y_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4837_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(v_ref_4827_, v_msg_4828_, v_declHint_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
    return v___x_4837_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___boxed(
    mut v_00_u03b1_4838_: *mut crate::leanh::LeanObject,
    mut v_ref_4839_: *mut crate::leanh::LeanObject,
    mut v_msg_4840_: *mut crate::leanh::LeanObject,
    mut v_declHint_4841_: *mut crate::leanh::LeanObject,
    mut v___y_4842_: *mut crate::leanh::LeanObject,
    mut v___y_4843_: *mut crate::leanh::LeanObject,
    mut v___y_4844_: *mut crate::leanh::LeanObject,
    mut v___y_4845_: *mut crate::leanh::LeanObject,
    mut v___y_4846_: *mut crate::leanh::LeanObject,
    mut v___y_4847_: *mut crate::leanh::LeanObject,
    mut v___y_4848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4849_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16(v_00_u03b1_4838_, v_ref_4839_, v_msg_4840_, v_declHint_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
    crate::leanh::lean_dec(v___y_4847_);
    crate::leanh::lean_dec_ref(v___y_4846_);
    crate::leanh::lean_dec(v___y_4845_);
    crate::leanh::lean_dec_ref(v___y_4844_);
    crate::leanh::lean_dec(v___y_4843_);
    crate::leanh::lean_dec(v___y_4842_);
    crate::leanh::lean_dec(v_ref_4839_);
    return v_res_4849_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18(
    mut v_msg_4850_: *mut crate::leanh::LeanObject,
    mut v_declHint_4851_: *mut crate::leanh::LeanObject,
    mut v___y_4852_: *mut crate::leanh::LeanObject,
    mut v___y_4853_: *mut crate::leanh::LeanObject,
    mut v___y_4854_: *mut crate::leanh::LeanObject,
    mut v___y_4855_: *mut crate::leanh::LeanObject,
    mut v___y_4856_: *mut crate::leanh::LeanObject,
    mut v___y_4857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4859_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_4850_, v_declHint_4851_, v___y_4857_);
    return v___x_4859_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___boxed(
    mut v_msg_4860_: *mut crate::leanh::LeanObject,
    mut v_declHint_4861_: *mut crate::leanh::LeanObject,
    mut v___y_4862_: *mut crate::leanh::LeanObject,
    mut v___y_4863_: *mut crate::leanh::LeanObject,
    mut v___y_4864_: *mut crate::leanh::LeanObject,
    mut v___y_4865_: *mut crate::leanh::LeanObject,
    mut v___y_4866_: *mut crate::leanh::LeanObject,
    mut v___y_4867_: *mut crate::leanh::LeanObject,
    mut v___y_4868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18(v_msg_4860_, v_declHint_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
    crate::leanh::lean_dec(v___y_4867_);
    crate::leanh::lean_dec_ref(v___y_4866_);
    crate::leanh::lean_dec(v___y_4865_);
    crate::leanh::lean_dec_ref(v___y_4864_);
    crate::leanh::lean_dec(v___y_4863_);
    crate::leanh::lean_dec(v___y_4862_);
    return v_res_4869_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18(
    mut v_00_u03b1_4870_: *mut crate::leanh::LeanObject,
    mut v_ref_4871_: *mut crate::leanh::LeanObject,
    mut v_msg_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
    mut v___y_4874_: *mut crate::leanh::LeanObject,
    mut v___y_4875_: *mut crate::leanh::LeanObject,
    mut v___y_4876_: *mut crate::leanh::LeanObject,
    mut v___y_4877_: *mut crate::leanh::LeanObject,
    mut v___y_4878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4880_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(v_ref_4871_, v_msg_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
    return v___x_4880_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___boxed(
    mut v_00_u03b1_4881_: *mut crate::leanh::LeanObject,
    mut v_ref_4882_: *mut crate::leanh::LeanObject,
    mut v_msg_4883_: *mut crate::leanh::LeanObject,
    mut v___y_4884_: *mut crate::leanh::LeanObject,
    mut v___y_4885_: *mut crate::leanh::LeanObject,
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4891_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18(v_00_u03b1_4881_, v_ref_4882_, v_msg_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
    crate::leanh::lean_dec(v___y_4889_);
    crate::leanh::lean_dec_ref(v___y_4888_);
    crate::leanh::lean_dec(v___y_4887_);
    crate::leanh::lean_dec_ref(v___y_4886_);
    crate::leanh::lean_dec(v___y_4885_);
    crate::leanh::lean_dec(v___y_4884_);
    crate::leanh::lean_dec(v_ref_4882_);
    return v_res_4891_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20(
    mut v_00_u03b1_4892_: *mut crate::leanh::LeanObject,
    mut v_msg_4893_: *mut crate::leanh::LeanObject,
    mut v___y_4894_: *mut crate::leanh::LeanObject,
    mut v___y_4895_: *mut crate::leanh::LeanObject,
    mut v___y_4896_: *mut crate::leanh::LeanObject,
    mut v___y_4897_: *mut crate::leanh::LeanObject,
    mut v___y_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(v_msg_4893_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
    return v___x_4901_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___boxed(
    mut v_00_u03b1_4902_: *mut crate::leanh::LeanObject,
    mut v_msg_4903_: *mut crate::leanh::LeanObject,
    mut v___y_4904_: *mut crate::leanh::LeanObject,
    mut v___y_4905_: *mut crate::leanh::LeanObject,
    mut v___y_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
    mut v___y_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4911_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20(v_00_u03b1_4902_, v_msg_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
    crate::leanh::lean_dec(v___y_4909_);
    crate::leanh::lean_dec_ref(v___y_4908_);
    crate::leanh::lean_dec(v___y_4907_);
    crate::leanh::lean_dec_ref(v___y_4906_);
    crate::leanh::lean_dec(v___y_4905_);
    crate::leanh::lean_dec(v___y_4904_);
    return v_res_4911_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0(
    mut v_recFnNames_4912_: *mut crate::leanh::LeanObject,
    mut v_e_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
    mut v___y_4919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4921_ = lean_st_ref_take(v___y_4914_);
    v___x_4922_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_4912_, v_e_4913_, v___x_4921_);
    v_fst_4923_ = crate::leanh::lean_ctor_get(v___x_4922_, 0);
    crate::leanh::lean_inc(v_fst_4923_);
    v_snd_4924_ = crate::leanh::lean_ctor_get(v___x_4922_, 1);
    crate::leanh::lean_inc(v_snd_4924_);
    crate::leanh::lean_dec_ref(v___x_4922_);
    v___x_4925_ = lean_st_ref_set(v___y_4914_, v_snd_4924_);
    v___x_4926_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4926_, 0, v_fst_4923_);
    return v___x_4926_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0___boxed(
    mut v_recFnNames_4927_: *mut crate::leanh::LeanObject,
    mut v_e_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
    mut v___y_4931_: *mut crate::leanh::LeanObject,
    mut v___y_4932_: *mut crate::leanh::LeanObject,
    mut v___y_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4936_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0(v_recFnNames_4927_, v_e_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
    crate::leanh::lean_dec(v___y_4934_);
    crate::leanh::lean_dec_ref(v___y_4933_);
    crate::leanh::lean_dec(v___y_4932_);
    crate::leanh::lean_dec_ref(v___y_4931_);
    crate::leanh::lean_dec(v___y_4930_);
    crate::leanh::lean_dec(v___y_4929_);
    crate::leanh::lean_dec_ref(v_recFnNames_4927_);
    return v_res_4936_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_spec__0(
    mut v_sz_4937_: usize,
    mut v_i_4938_: usize,
    mut v_bs_4939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4940_: u8 = 0;
    let mut v_v_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnName_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: usize = 0;
    let mut v___x_4946_: usize = 0;
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4940_ = lean_usize_dec_lt(v_i_4938_, v_sz_4937_);
                if v___x_4940_ == 0 {
                    return v_bs_4939_;
                } else {
                    v_v_4941_ = lean_array_uget_borrowed(v_bs_4939_, v_i_4938_);
                    v_fnName_4942_ = crate::leanh::lean_ctor_get(v_v_4941_, 0);
                    crate::leanh::lean_inc(v_fnName_4942_);
                    v___x_4943_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4944_ = lean_array_uset(v_bs_4939_, v_i_4938_, v___x_4943_);
                    v___x_4945_ = 1usize;
                    v___x_4946_ = lean_usize_add(v_i_4938_, v___x_4945_);
                    v___x_4947_ = lean_array_uset(v_bs_x27_4944_, v_i_4938_, v_fnName_4942_);
                    v_i_4938_ = v___x_4946_;
                    v_bs_4939_ = v___x_4947_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_spec__0___boxed(
    mut v_sz_4949_: *mut crate::leanh::LeanObject,
    mut v_i_4950_: *mut crate::leanh::LeanObject,
    mut v_bs_4951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4952_: usize = 0;
    let mut v_i_boxed_4953_: usize = 0;
    let mut v_res_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4952_ = crate::leanh::lean_unbox_usize(v_sz_4949_);
    crate::leanh::lean_dec(v_sz_4949_);
    v_i_boxed_4953_ = crate::leanh::lean_unbox_usize(v_i_4950_);
    crate::leanh::lean_dec(v_i_4950_);
    v_res_4954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_spec__0(v_sz_boxed_4952_, v_i_boxed_4953_, v_bs_4951_);
    return v_res_4954_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4955_ = crate::leanh::lean_box(0);
    v___x_4956_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4957_ = lean_mk_array(v___x_4956_, v___x_4955_);
    return v___x_4957_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4958_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0);
    v___x_4959_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4960_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4960_, 0, v___x_4959_);
    crate::leanh::lean_ctor_set(v___x_4960_, 1, v___x_4958_);
    return v___x_4960_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps(
    mut v_recArgInfos_4961_: *mut crate::leanh::LeanObject,
    mut v_positions_4962_: *mut crate::leanh::LeanObject,
    mut v_params_4963_: *mut crate::leanh::LeanObject,
    mut v_ctx_4964_: *mut crate::leanh::LeanObject,
    mut v_e_4965_: *mut crate::leanh::LeanObject,
    mut v_a_4966_: *mut crate::leanh::LeanObject,
    mut v_a_4967_: *mut crate::leanh::LeanObject,
    mut v_a_4968_: *mut crate::leanh::LeanObject,
    mut v_a_4969_: *mut crate::leanh::LeanObject,
    mut v_a_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4974_: usize = 0;
    let mut v___x_4975_: usize = 0;
    let mut v_recFnNames_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_containsRecFn_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4982_: u8 = 0;
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4972_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1);
                v___x_4973_ = lean_st_mk_ref(v___x_4972_);
                v_sz_4974_ = lean_array_size(v_recArgInfos_4961_);
                v___x_4975_ = 0usize;
                crate::leanh::lean_inc_ref(v_recArgInfos_4961_);
                v_recFnNames_4976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_spec__0(v_sz_4974_, v___x_4975_, v_recArgInfos_4961_);
                crate::leanh::lean_inc_ref(v_recFnNames_4976_);
                v_containsRecFn_4977_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                crate::leanh::lean_closure_set(v_containsRecFn_4977_, 0, v_recFnNames_4976_);
                crate::leanh::lean_inc_ref(v_a_4969_);
                v___x_4978_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4961_, v_positions_4962_, v_params_4963_, v_recFnNames_4976_, v_containsRecFn_4977_, v_ctx_4964_, v_e_4965_, v___x_4973_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
                if crate::leanh::lean_obj_tag(v___x_4978_) == 0 {
                    v_a_4979_ = crate::leanh::lean_ctor_get(v___x_4978_, 0);
                    v_isSharedCheck_4987_ = (!crate::leanh::lean_is_exclusive(v___x_4978_)) as u8;
                    if v_isSharedCheck_4987_ == 0 {
                        v___x_4981_ = v___x_4978_;
                        v_isShared_4982_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4979_);
                        crate::leanh::lean_dec(v___x_4978_);
                        v___x_4981_ = crate::leanh::lean_box(0);
                        v_isShared_4982_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4973_);
                    return v___x_4978_;
                }
            }
            1 => {
                v___x_4983_ = lean_st_ref_get(v___x_4973_);
                crate::leanh::lean_dec(v___x_4973_);
                crate::leanh::lean_dec(v___x_4983_);
                if v_isShared_4982_ == 0 {
                    v___x_4985_ = v___x_4981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4986_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4979_);
                    v___x_4985_ = v_reuseFailAlloc_4986_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4985_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___boxed(
    mut v_recArgInfos_4988_: *mut crate::leanh::LeanObject,
    mut v_positions_4989_: *mut crate::leanh::LeanObject,
    mut v_params_4990_: *mut crate::leanh::LeanObject,
    mut v_ctx_4991_: *mut crate::leanh::LeanObject,
    mut v_e_4992_: *mut crate::leanh::LeanObject,
    mut v_a_4993_: *mut crate::leanh::LeanObject,
    mut v_a_4994_: *mut crate::leanh::LeanObject,
    mut v_a_4995_: *mut crate::leanh::LeanObject,
    mut v_a_4996_: *mut crate::leanh::LeanObject,
    mut v_a_4997_: *mut crate::leanh::LeanObject,
    mut v_a_4998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4999_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps(v_recArgInfos_4988_, v_positions_4989_, v_params_4990_, v_ctx_4991_, v_e_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
    crate::leanh::lean_dec(v_a_4997_);
    crate::leanh::lean_dec_ref(v_a_4996_);
    crate::leanh::lean_dec(v_a_4995_);
    crate::leanh::lean_dec_ref(v_a_4994_);
    crate::leanh::lean_dec(v_a_4993_);
    return v_res_4999_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0(
    mut v_k_5000_: *mut crate::leanh::LeanObject,
    mut v_b_5001_: *mut crate::leanh::LeanObject,
    mut v___y_5002_: *mut crate::leanh::LeanObject,
    mut v___y_5003_: *mut crate::leanh::LeanObject,
    mut v___y_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5005_);
    crate::leanh::lean_inc_ref(v___y_5004_);
    crate::leanh::lean_inc(v___y_5003_);
    crate::leanh::lean_inc_ref(v___y_5002_);
    v___x_5007_ = crate::leanh::lean_apply_6(
        v_k_5000_,
        v_b_5001_,
        v___y_5002_,
        v___y_5003_,
        v___y_5004_,
        v___y_5005_,
        crate::leanh::lean_box(0),
    );
    return v___x_5007_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0___boxed(
    mut v_k_5008_: *mut crate::leanh::LeanObject,
    mut v_b_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
    mut v___y_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
    mut v___y_5014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5015_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0(v_k_5008_, v_b_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
    crate::leanh::lean_dec(v___y_5013_);
    crate::leanh::lean_dec_ref(v___y_5012_);
    crate::leanh::lean_dec(v___y_5011_);
    crate::leanh::lean_dec_ref(v___y_5010_);
    return v_res_5015_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(
    mut v_name_5016_: *mut crate::leanh::LeanObject,
    mut v_type_5017_: *mut crate::leanh::LeanObject,
    mut v_val_5018_: *mut crate::leanh::LeanObject,
    mut v_k_5019_: *mut crate::leanh::LeanObject,
    mut v_nondep_5020_: u8,
    mut v_kind_5021_: u8,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
    mut v___y_5024_: *mut crate::leanh::LeanObject,
    mut v___y_5025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5027_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_5027_, 0, v_k_5019_);
                v___x_5028_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_5016_,
                    v_type_5017_,
                    v_val_5018_,
                    v___f_5027_,
                    v_nondep_5020_,
                    v_kind_5021_,
                    v___y_5022_,
                    v___y_5023_,
                    v___y_5024_,
                    v___y_5025_,
                );
                if crate::leanh::lean_obj_tag(v___x_5028_) == 0 {
                    v_a_5029_ = crate::leanh::lean_ctor_get(v___x_5028_, 0);
                    v_isSharedCheck_5036_ = (!crate::leanh::lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v___x_5031_ = v___x_5028_;
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5029_);
                        crate::leanh::lean_dec(v___x_5028_);
                        v___x_5031_ = crate::leanh::lean_box(0);
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5037_ = crate::leanh::lean_ctor_get(v___x_5028_, 0);
                    v_isSharedCheck_5044_ = (!crate::leanh::lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5044_ == 0 {
                        v___x_5039_ = v___x_5028_;
                        v_isShared_5040_ = v_isSharedCheck_5044_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5037_);
                        crate::leanh::lean_dec(v___x_5028_);
                        v___x_5039_ = crate::leanh::lean_box(0);
                        v_isShared_5040_ = v_isSharedCheck_5044_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5032_ == 0 {
                    v___x_5034_ = v___x_5031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
                    v___x_5034_ = v_reuseFailAlloc_5035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5034_;
            }
            3 => {
                if v_isShared_5040_ == 0 {
                    v___x_5042_ = v___x_5039_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
                    v___x_5042_ = v_reuseFailAlloc_5043_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5042_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___boxed(
    mut v_name_5045_: *mut crate::leanh::LeanObject,
    mut v_type_5046_: *mut crate::leanh::LeanObject,
    mut v_val_5047_: *mut crate::leanh::LeanObject,
    mut v_k_5048_: *mut crate::leanh::LeanObject,
    mut v_nondep_5049_: *mut crate::leanh::LeanObject,
    mut v_kind_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_5056_: u8 = 0;
    let mut v_kind_boxed_5057_: u8 = 0;
    let mut v_res_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5056_ = (crate::leanh::lean_unbox(v_nondep_5049_) as u8);
    v_kind_boxed_5057_ = (crate::leanh::lean_unbox(v_kind_5050_) as u8);
    v_res_5058_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(v_name_5045_, v_type_5046_, v_val_5047_, v_k_5048_, v_nondep_boxed_5056_, v_kind_boxed_5057_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
    crate::leanh::lean_dec(v___y_5054_);
    crate::leanh::lean_dec_ref(v___y_5053_);
    crate::leanh::lean_dec(v___y_5052_);
    crate::leanh::lean_dec_ref(v___y_5051_);
    return v_res_5058_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0(
    mut v_00_u03b1_5059_: *mut crate::leanh::LeanObject,
    mut v_name_5060_: *mut crate::leanh::LeanObject,
    mut v_type_5061_: *mut crate::leanh::LeanObject,
    mut v_val_5062_: *mut crate::leanh::LeanObject,
    mut v_k_5063_: *mut crate::leanh::LeanObject,
    mut v_nondep_5064_: u8,
    mut v_kind_5065_: u8,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5071_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(v_name_5060_, v_type_5061_, v_val_5062_, v_k_5063_, v_nondep_5064_, v_kind_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
    return v___x_5071_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___boxed(
    mut v_00_u03b1_5072_: *mut crate::leanh::LeanObject,
    mut v_name_5073_: *mut crate::leanh::LeanObject,
    mut v_type_5074_: *mut crate::leanh::LeanObject,
    mut v_val_5075_: *mut crate::leanh::LeanObject,
    mut v_k_5076_: *mut crate::leanh::LeanObject,
    mut v_nondep_5077_: *mut crate::leanh::LeanObject,
    mut v_kind_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
    mut v___y_5082_: *mut crate::leanh::LeanObject,
    mut v___y_5083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_5084_: u8 = 0;
    let mut v_kind_boxed_5085_: u8 = 0;
    let mut v_res_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5084_ = (crate::leanh::lean_unbox(v_nondep_5077_) as u8);
    v_kind_boxed_5085_ = (crate::leanh::lean_unbox(v_kind_5078_) as u8);
    v_res_5086_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0(v_00_u03b1_5072_, v_name_5073_, v_type_5074_, v_val_5075_, v_k_5076_, v_nondep_boxed_5084_, v_kind_boxed_5085_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
    crate::leanh::lean_dec(v___y_5082_);
    crate::leanh::lean_dec_ref(v___y_5081_);
    crate::leanh::lean_dec(v___y_5080_);
    crate::leanh::lean_dec_ref(v___y_5079_);
    return v_res_5086_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0(
    mut v_k_5087_: *mut crate::leanh::LeanObject,
    mut v_b_5088_: *mut crate::leanh::LeanObject,
    mut v_c_5089_: *mut crate::leanh::LeanObject,
    mut v___y_5090_: *mut crate::leanh::LeanObject,
    mut v___y_5091_: *mut crate::leanh::LeanObject,
    mut v___y_5092_: *mut crate::leanh::LeanObject,
    mut v___y_5093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5093_);
    crate::leanh::lean_inc_ref(v___y_5092_);
    crate::leanh::lean_inc(v___y_5091_);
    crate::leanh::lean_inc_ref(v___y_5090_);
    v___x_5095_ = crate::leanh::lean_apply_7(
        v_k_5087_,
        v_b_5088_,
        v_c_5089_,
        v___y_5090_,
        v___y_5091_,
        v___y_5092_,
        v___y_5093_,
        crate::leanh::lean_box(0),
    );
    return v___x_5095_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0___boxed(
    mut v_k_5096_: *mut crate::leanh::LeanObject,
    mut v_b_5097_: *mut crate::leanh::LeanObject,
    mut v_c_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
    mut v___y_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5104_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0(v_k_5096_, v_b_5097_, v_c_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
    crate::leanh::lean_dec(v___y_5102_);
    crate::leanh::lean_dec_ref(v___y_5101_);
    crate::leanh::lean_dec(v___y_5100_);
    crate::leanh::lean_dec_ref(v___y_5099_);
    return v_res_5104_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(
    mut v_e_5105_: *mut crate::leanh::LeanObject,
    mut v_k_5106_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5107_: u8,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut v_a_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5129_: u8 = 0;
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5113_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_5113_, 0, v_k_5106_);
                v___x_5114_ = 1;
                v___x_5115_ = 0;
                v___x_5116_ = crate::leanh::lean_box(0);
                v___x_5117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
                    v_e_5105_,
                    v___x_5114_,
                    v___x_5115_,
                    v___x_5114_,
                    v___x_5115_,
                    v___x_5116_,
                    v___f_5113_,
                    v_cleanupAnnotations_5107_,
                    v___y_5108_,
                    v___y_5109_,
                    v___y_5110_,
                    v___y_5111_,
                );
                if crate::leanh::lean_obj_tag(v___x_5117_) == 0 {
                    v_a_5118_ = crate::leanh::lean_ctor_get(v___x_5117_, 0);
                    v_isSharedCheck_5125_ = (!crate::leanh::lean_is_exclusive(v___x_5117_)) as u8;
                    if v_isSharedCheck_5125_ == 0 {
                        v___x_5120_ = v___x_5117_;
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5118_);
                        crate::leanh::lean_dec(v___x_5117_);
                        v___x_5120_ = crate::leanh::lean_box(0);
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5126_ = crate::leanh::lean_ctor_get(v___x_5117_, 0);
                    v_isSharedCheck_5133_ = (!crate::leanh::lean_is_exclusive(v___x_5117_)) as u8;
                    if v_isSharedCheck_5133_ == 0 {
                        v___x_5128_ = v___x_5117_;
                        v_isShared_5129_ = v_isSharedCheck_5133_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5126_);
                        crate::leanh::lean_dec(v___x_5117_);
                        v___x_5128_ = crate::leanh::lean_box(0);
                        v_isShared_5129_ = v_isSharedCheck_5133_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5121_ == 0 {
                    v___x_5123_ = v___x_5120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
                    v___x_5123_ = v_reuseFailAlloc_5124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5123_;
            }
            3 => {
                if v_isShared_5129_ == 0 {
                    v___x_5131_ = v___x_5128_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
                    v___x_5131_ = v_reuseFailAlloc_5132_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___boxed(
    mut v_e_5134_: *mut crate::leanh::LeanObject,
    mut v_k_5135_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5142_: u8 = 0;
    let mut v_res_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5142_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_5136_) as u8);
    v_res_5143_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_e_5134_, v_k_5135_, v_cleanupAnnotations_boxed_5142_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
    crate::leanh::lean_dec(v___y_5140_);
    crate::leanh::lean_dec_ref(v___y_5139_);
    crate::leanh::lean_dec(v___y_5138_);
    crate::leanh::lean_dec_ref(v___y_5137_);
    return v_res_5143_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1(
    mut v_00_u03b1_5144_: *mut crate::leanh::LeanObject,
    mut v_e_5145_: *mut crate::leanh::LeanObject,
    mut v_k_5146_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5147_: u8,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
    mut v___y_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5153_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_e_5145_, v_k_5146_, v_cleanupAnnotations_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_);
    return v___x_5153_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___boxed(
    mut v_00_u03b1_5154_: *mut crate::leanh::LeanObject,
    mut v_e_5155_: *mut crate::leanh::LeanObject,
    mut v_k_5156_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5163_: u8 = 0;
    let mut v_res_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5163_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_5157_) as u8);
    v_res_5164_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1(v_00_u03b1_5154_, v_e_5155_, v_k_5156_, v_cleanupAnnotations_boxed_5163_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
    crate::leanh::lean_dec(v___y_5161_);
    crate::leanh::lean_dec_ref(v___y_5160_);
    crate::leanh::lean_dec(v___y_5159_);
    crate::leanh::lean_dec_ref(v___y_5158_);
    return v_res_5164_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0___boxed(
    mut v_res_5168_: *mut crate::leanh::LeanObject,
    mut v_values_5169_: *mut crate::leanh::LeanObject,
    mut v_k_5170_: *mut crate::leanh::LeanObject,
    mut v___x_5171_: *mut crate::leanh::LeanObject,
    mut v_funType_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
    mut v___y_5176_: *mut crate::leanh::LeanObject,
    mut v___y_5177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5178_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0(v_res_5168_, v_values_5169_, v_k_5170_, v___x_5171_, v_funType_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
    crate::leanh::lean_dec(v___y_5176_);
    crate::leanh::lean_dec_ref(v___y_5175_);
    crate::leanh::lean_dec(v___y_5174_);
    crate::leanh::lean_dec_ref(v___y_5173_);
    return v_res_5178_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1(
    mut v___x_5179_: u8,
    mut v_i_5180_: *mut crate::leanh::LeanObject,
    mut v_res_5181_: *mut crate::leanh::LeanObject,
    mut v_values_5182_: *mut crate::leanh::LeanObject,
    mut v_k_5183_: *mut crate::leanh::LeanObject,
    mut v_xs_5184_: *mut crate::leanh::LeanObject,
    mut v_value_5185_: *mut crate::leanh::LeanObject,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
    mut v___y_5189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: u8 = 0;
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: u8 = 0;
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5210_: u8 = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_a_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5218_: u8 = 0;
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut v_a_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5226_: u8 = 0;
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5189_);
                crate::leanh::lean_inc_ref(v___y_5188_);
                crate::leanh::lean_inc(v___y_5187_);
                crate::leanh::lean_inc_ref(v___y_5186_);
                v___x_5191_ = lean_infer_type(
                    v_value_5185_,
                    v___y_5186_,
                    v___y_5187_,
                    v___y_5188_,
                    v___y_5189_,
                );
                if crate::leanh::lean_obj_tag(v___x_5191_) == 0 {
                    v_a_5192_ = crate::leanh::lean_ctor_get(v___x_5191_, 0);
                    crate::leanh::lean_inc(v_a_5192_);
                    crate::leanh::lean_dec_ref_known(v___x_5191_, 1);
                    v___x_5193_ = l_Lean_Expr_headBeta(v_a_5192_);
                    v___x_5194_ = 0;
                    v___x_5195_ = 1;
                    v___x_5196_ = l_Lean_Meta_mkLambdaFVars(
                        v_xs_5184_,
                        v___x_5193_,
                        v___x_5194_,
                        v___x_5179_,
                        v___x_5194_,
                        v___x_5179_,
                        v___x_5195_,
                        v___y_5186_,
                        v___y_5187_,
                        v___y_5188_,
                        v___y_5189_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5196_) == 0 {
                        v_a_5197_ = crate::leanh::lean_ctor_get(v___x_5196_, 0);
                        crate::leanh::lean_inc_n(v_a_5197_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5196_, 1);
                        crate::leanh::lean_inc(v___y_5189_);
                        crate::leanh::lean_inc_ref(v___y_5188_);
                        crate::leanh::lean_inc(v___y_5187_);
                        crate::leanh::lean_inc_ref(v___y_5186_);
                        v___x_5198_ = lean_infer_type(
                            v_a_5197_,
                            v___y_5186_,
                            v___y_5187_,
                            v___y_5188_,
                            v___y_5189_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5198_) == 0 {
                            v_a_5199_ = crate::leanh::lean_ctor_get(v___x_5198_, 0);
                            crate::leanh::lean_inc(v_a_5199_);
                            crate::leanh::lean_dec_ref_known(v___x_5198_, 1);
                            v___x_5200_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1;
                            v___x_5201_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_5202_ = lean_nat_add(v_i_5180_, v___x_5201_);
                            crate::leanh::lean_inc(v___x_5202_);
                            v___f_5203_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                            crate::leanh::lean_closure_set(v___f_5203_, 0, v_res_5181_);
                            crate::leanh::lean_closure_set(v___f_5203_, 1, v_values_5182_);
                            crate::leanh::lean_closure_set(v___f_5203_, 2, v_k_5183_);
                            crate::leanh::lean_closure_set(v___f_5203_, 3, v___x_5202_);
                            v___x_5204_ = lean_name_append_index_after(v___x_5200_, v___x_5202_);
                            v___x_5205_ = 0;
                            v___x_5206_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(v___x_5204_, v_a_5199_, v_a_5197_, v___f_5203_, v___x_5194_, v___x_5205_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
                            return v___x_5206_;
                        } else {
                            crate::leanh::lean_dec(v_a_5197_);
                            crate::leanh::lean_dec_ref(v_k_5183_);
                            crate::leanh::lean_dec_ref(v_values_5182_);
                            crate::leanh::lean_dec_ref(v_res_5181_);
                            v_a_5207_ = crate::leanh::lean_ctor_get(v___x_5198_, 0);
                            v_isSharedCheck_5214_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5198_)) as u8;
                            if v_isSharedCheck_5214_ == 0 {
                                v___x_5209_ = v___x_5198_;
                                v_isShared_5210_ = v_isSharedCheck_5214_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5207_);
                                crate::leanh::lean_dec(v___x_5198_);
                                v___x_5209_ = crate::leanh::lean_box(0);
                                v_isShared_5210_ = v_isSharedCheck_5214_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5183_);
                        crate::leanh::lean_dec_ref(v_values_5182_);
                        crate::leanh::lean_dec_ref(v_res_5181_);
                        v_a_5215_ = crate::leanh::lean_ctor_get(v___x_5196_, 0);
                        v_isSharedCheck_5222_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5196_)) as u8;
                        if v_isSharedCheck_5222_ == 0 {
                            v___x_5217_ = v___x_5196_;
                            v_isShared_5218_ = v_isSharedCheck_5222_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5215_);
                            crate::leanh::lean_dec(v___x_5196_);
                            v___x_5217_ = crate::leanh::lean_box(0);
                            v_isShared_5218_ = v_isSharedCheck_5222_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_5183_);
                    crate::leanh::lean_dec_ref(v_values_5182_);
                    crate::leanh::lean_dec_ref(v_res_5181_);
                    v_a_5223_ = crate::leanh::lean_ctor_get(v___x_5191_, 0);
                    v_isSharedCheck_5230_ = (!crate::leanh::lean_is_exclusive(v___x_5191_)) as u8;
                    if v_isSharedCheck_5230_ == 0 {
                        v___x_5225_ = v___x_5191_;
                        v_isShared_5226_ = v_isSharedCheck_5230_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5223_);
                        crate::leanh::lean_dec(v___x_5191_);
                        v___x_5225_ = crate::leanh::lean_box(0);
                        v_isShared_5226_ = v_isSharedCheck_5230_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5210_ == 0 {
                    v___x_5212_ = v___x_5209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
                    v___x_5212_ = v_reuseFailAlloc_5213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5212_;
            }
            3 => {
                if v_isShared_5218_ == 0 {
                    v___x_5220_ = v___x_5217_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
                    v___x_5220_ = v_reuseFailAlloc_5221_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5220_;
            }
            5 => {
                if v_isShared_5226_ == 0 {
                    v___x_5228_ = v___x_5225_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_a_5223_);
                    v___x_5228_ = v_reuseFailAlloc_5229_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___boxed(
    mut v___x_5231_: *mut crate::leanh::LeanObject,
    mut v_i_5232_: *mut crate::leanh::LeanObject,
    mut v_res_5233_: *mut crate::leanh::LeanObject,
    mut v_values_5234_: *mut crate::leanh::LeanObject,
    mut v_k_5235_: *mut crate::leanh::LeanObject,
    mut v_xs_5236_: *mut crate::leanh::LeanObject,
    mut v_value_5237_: *mut crate::leanh::LeanObject,
    mut v___y_5238_: *mut crate::leanh::LeanObject,
    mut v___y_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1255__boxed_5243_: u8 = 0;
    let mut v_res_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255__boxed_5243_ = (crate::leanh::lean_unbox(v___x_5231_) as u8);
    v_res_5244_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1(v___x_1255__boxed_5243_, v_i_5232_, v_res_5233_, v_values_5234_, v_k_5235_, v_xs_5236_, v_value_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_);
    crate::leanh::lean_dec(v___y_5241_);
    crate::leanh::lean_dec_ref(v___y_5240_);
    crate::leanh::lean_dec(v___y_5239_);
    crate::leanh::lean_dec_ref(v___y_5238_);
    crate::leanh::lean_dec_ref(v_xs_5236_);
    crate::leanh::lean_dec(v_i_5232_);
    return v_res_5244_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(
    mut v_values_5245_: *mut crate::leanh::LeanObject,
    mut v_k_5246_: *mut crate::leanh::LeanObject,
    mut v_i_5247_: *mut crate::leanh::LeanObject,
    mut v_res_5248_: *mut crate::leanh::LeanObject,
    mut v_a_5249_: *mut crate::leanh::LeanObject,
    mut v_a_5250_: *mut crate::leanh::LeanObject,
    mut v_a_5251_: *mut crate::leanh::LeanObject,
    mut v_a_5252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: u8 = 0;
    v___x_5254_ = lean_array_get_size(v_values_5245_);
    v___x_5255_ = lean_nat_dec_lt(v_i_5247_, v___x_5254_);
    if v___x_5255_ == 0 {
        let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_5247_);
        crate::leanh::lean_dec_ref(v_values_5245_);
        crate::leanh::lean_inc(v_a_5252_);
        crate::leanh::lean_inc_ref(v_a_5251_);
        crate::leanh::lean_inc(v_a_5250_);
        crate::leanh::lean_inc_ref(v_a_5249_);
        v___x_5256_ = crate::leanh::lean_apply_6(
            v_k_5246_,
            v_res_5248_,
            v_a_5249_,
            v_a_5250_,
            v_a_5251_,
            v_a_5252_,
            crate::leanh::lean_box(0),
        );
        return v___x_5256_;
    } else {
        let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5260_: u8 = 0;
        let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5257_ = crate::leanh::lean_box((v___x_5255_) as usize);
        crate::leanh::lean_inc_ref(v_values_5245_);
        crate::leanh::lean_inc(v_i_5247_);
        v___f_5258_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 12, 5);
        crate::leanh::lean_closure_set(v___f_5258_, 0, v___x_5257_);
        crate::leanh::lean_closure_set(v___f_5258_, 1, v_i_5247_);
        crate::leanh::lean_closure_set(v___f_5258_, 2, v_res_5248_);
        crate::leanh::lean_closure_set(v___f_5258_, 3, v_values_5245_);
        crate::leanh::lean_closure_set(v___f_5258_, 4, v_k_5246_);
        v___x_5259_ = lean_array_fget(v_values_5245_, v_i_5247_);
        crate::leanh::lean_dec(v_i_5247_);
        crate::leanh::lean_dec_ref(v_values_5245_);
        v___x_5260_ = 0;
        v___x_5261_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v___x_5259_, v___f_5258_, v___x_5260_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_);
        return v___x_5261_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0(
    mut v_res_5262_: *mut crate::leanh::LeanObject,
    mut v_values_5263_: *mut crate::leanh::LeanObject,
    mut v_k_5264_: *mut crate::leanh::LeanObject,
    mut v___x_5265_: *mut crate::leanh::LeanObject,
    mut v_funType_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
    mut v___y_5270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5272_ = lean_array_push(v_res_5262_, v_funType_5266_);
    v___x_5273_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5263_, v_k_5264_, v___x_5265_, v___x_5272_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
    return v___x_5273_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___boxed(
    mut v_values_5274_: *mut crate::leanh::LeanObject,
    mut v_k_5275_: *mut crate::leanh::LeanObject,
    mut v_i_5276_: *mut crate::leanh::LeanObject,
    mut v_res_5277_: *mut crate::leanh::LeanObject,
    mut v_a_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
    mut v_a_5281_: *mut crate::leanh::LeanObject,
    mut v_a_5282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5283_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5274_, v_k_5275_, v_i_5276_, v_res_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
    crate::leanh::lean_dec(v_a_5281_);
    crate::leanh::lean_dec_ref(v_a_5280_);
    crate::leanh::lean_dec(v_a_5279_);
    crate::leanh::lean_dec_ref(v_a_5278_);
    return v_res_5283_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go(
    mut v_00_u03b1_5284_: *mut crate::leanh::LeanObject,
    mut v_values_5285_: *mut crate::leanh::LeanObject,
    mut v_k_5286_: *mut crate::leanh::LeanObject,
    mut v_i_5287_: *mut crate::leanh::LeanObject,
    mut v_res_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5294_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5285_, v_k_5286_, v_i_5287_, v_res_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
    return v___x_5294_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___boxed(
    mut v_00_u03b1_5295_: *mut crate::leanh::LeanObject,
    mut v_values_5296_: *mut crate::leanh::LeanObject,
    mut v_k_5297_: *mut crate::leanh::LeanObject,
    mut v_i_5298_: *mut crate::leanh::LeanObject,
    mut v_res_5299_: *mut crate::leanh::LeanObject,
    mut v_a_5300_: *mut crate::leanh::LeanObject,
    mut v_a_5301_: *mut crate::leanh::LeanObject,
    mut v_a_5302_: *mut crate::leanh::LeanObject,
    mut v_a_5303_: *mut crate::leanh::LeanObject,
    mut v_a_5304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5305_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go(v_00_u03b1_5295_, v_values_5296_, v_k_5297_, v_i_5298_, v_res_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
    crate::leanh::lean_dec(v_a_5303_);
    crate::leanh::lean_dec_ref(v_a_5302_);
    crate::leanh::lean_dec(v_a_5301_);
    crate::leanh::lean_dec_ref(v_a_5300_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_Elab_Structural_withFunTypes___redArg(
    mut v_values_5306_: *mut crate::leanh::LeanObject,
    mut v_k_5307_: *mut crate::leanh::LeanObject,
    mut v_a_5308_: *mut crate::leanh::LeanObject,
    mut v_a_5309_: *mut crate::leanh::LeanObject,
    mut v_a_5310_: *mut crate::leanh::LeanObject,
    mut v_a_5311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5313_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5314_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5;
    v___x_5315_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5306_, v_k_5307_, v___x_5313_, v___x_5314_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_);
    return v___x_5315_;
}
pub unsafe fn l_Lean_Elab_Structural_withFunTypes___redArg___boxed(
    mut v_values_5316_: *mut crate::leanh::LeanObject,
    mut v_k_5317_: *mut crate::leanh::LeanObject,
    mut v_a_5318_: *mut crate::leanh::LeanObject,
    mut v_a_5319_: *mut crate::leanh::LeanObject,
    mut v_a_5320_: *mut crate::leanh::LeanObject,
    mut v_a_5321_: *mut crate::leanh::LeanObject,
    mut v_a_5322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5323_ = l_Lean_Elab_Structural_withFunTypes___redArg(
        v_values_5316_,
        v_k_5317_,
        v_a_5318_,
        v_a_5319_,
        v_a_5320_,
        v_a_5321_,
    );
    crate::leanh::lean_dec(v_a_5321_);
    crate::leanh::lean_dec_ref(v_a_5320_);
    crate::leanh::lean_dec(v_a_5319_);
    crate::leanh::lean_dec_ref(v_a_5318_);
    return v_res_5323_;
}
pub unsafe fn l_Lean_Elab_Structural_withFunTypes(
    mut v_00_u03b1_5324_: *mut crate::leanh::LeanObject,
    mut v_values_5325_: *mut crate::leanh::LeanObject,
    mut v_k_5326_: *mut crate::leanh::LeanObject,
    mut v_a_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5332_ = l_Lean_Elab_Structural_withFunTypes___redArg(
        v_values_5325_,
        v_k_5326_,
        v_a_5327_,
        v_a_5328_,
        v_a_5329_,
        v_a_5330_,
    );
    return v___x_5332_;
}
pub unsafe fn l_Lean_Elab_Structural_withFunTypes___boxed(
    mut v_00_u03b1_5333_: *mut crate::leanh::LeanObject,
    mut v_values_5334_: *mut crate::leanh::LeanObject,
    mut v_k_5335_: *mut crate::leanh::LeanObject,
    mut v_a_5336_: *mut crate::leanh::LeanObject,
    mut v_a_5337_: *mut crate::leanh::LeanObject,
    mut v_a_5338_: *mut crate::leanh::LeanObject,
    mut v_a_5339_: *mut crate::leanh::LeanObject,
    mut v_a_5340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5341_ = l_Lean_Elab_Structural_withFunTypes(
        v_00_u03b1_5333_,
        v_values_5334_,
        v_k_5335_,
        v_a_5336_,
        v_a_5337_,
        v_a_5338_,
        v_a_5339_,
    );
    crate::leanh::lean_dec(v_a_5339_);
    crate::leanh::lean_dec_ref(v_a_5338_);
    crate::leanh::lean_dec(v_a_5337_);
    crate::leanh::lean_dec_ref(v_a_5336_);
    return v_res_5341_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive___lam__0(
    mut v_funType_5342_: *mut crate::leanh::LeanObject,
    mut v_recArgInfo_5343_: *mut crate::leanh::LeanObject,
    mut v_xs_5344_: *mut crate::leanh::LeanObject,
    mut v_x_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
    mut v___y_5347_: *mut crate::leanh::LeanObject,
    mut v___y_5348_: *mut crate::leanh::LeanObject,
    mut v___y_5349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: u8 = 0;
    let mut v___x_5356_: u8 = 0;
    let mut v___x_5357_: u8 = 0;
    let mut v___x_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_5351_ = l_Lean_mkAppN(v_funType_5342_, v_xs_5344_);
    v___x_5352_ =
        l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_5343_, v_xs_5344_);
    v_fst_5353_ = crate::leanh::lean_ctor_get(v___x_5352_, 0);
    crate::leanh::lean_inc(v_fst_5353_);
    v_snd_5354_ = crate::leanh::lean_ctor_get(v___x_5352_, 1);
    crate::leanh::lean_inc(v_snd_5354_);
    crate::leanh::lean_dec_ref(v___x_5352_);
    v___x_5355_ = 0;
    v___x_5356_ = 1;
    v___x_5357_ = 1;
    v___x_5358_ = l_Lean_Meta_mkForallFVars(
        v_snd_5354_,
        v_type_5351_,
        v___x_5355_,
        v___x_5356_,
        v___x_5356_,
        v___x_5357_,
        v___y_5346_,
        v___y_5347_,
        v___y_5348_,
        v___y_5349_,
    );
    crate::leanh::lean_dec(v_snd_5354_);
    if crate::leanh::lean_obj_tag(v___x_5358_) == 0 {
        let mut v_a_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5359_ = crate::leanh::lean_ctor_get(v___x_5358_, 0);
        crate::leanh::lean_inc(v_a_5359_);
        crate::leanh::lean_dec_ref_known(v___x_5358_, 1);
        v___x_5360_ = l_Lean_Meta_mkLambdaFVars(
            v_fst_5353_,
            v_a_5359_,
            v___x_5355_,
            v___x_5356_,
            v___x_5355_,
            v___x_5356_,
            v___x_5357_,
            v___y_5346_,
            v___y_5347_,
            v___y_5348_,
            v___y_5349_,
        );
        crate::leanh::lean_dec(v_fst_5353_);
        return v___x_5360_;
    } else {
        crate::leanh::lean_dec(v_fst_5353_);
        return v___x_5358_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive___lam__0___boxed(
    mut v_funType_5361_: *mut crate::leanh::LeanObject,
    mut v_recArgInfo_5362_: *mut crate::leanh::LeanObject,
    mut v_xs_5363_: *mut crate::leanh::LeanObject,
    mut v_x_5364_: *mut crate::leanh::LeanObject,
    mut v___y_5365_: *mut crate::leanh::LeanObject,
    mut v___y_5366_: *mut crate::leanh::LeanObject,
    mut v___y_5367_: *mut crate::leanh::LeanObject,
    mut v___y_5368_: *mut crate::leanh::LeanObject,
    mut v___y_5369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5370_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive___lam__0(
        v_funType_5361_,
        v_recArgInfo_5362_,
        v_xs_5363_,
        v_x_5364_,
        v___y_5365_,
        v___y_5366_,
        v___y_5367_,
        v___y_5368_,
    );
    crate::leanh::lean_dec(v___y_5368_);
    crate::leanh::lean_dec_ref(v___y_5367_);
    crate::leanh::lean_dec(v___y_5366_);
    crate::leanh::lean_dec_ref(v___y_5365_);
    crate::leanh::lean_dec_ref(v_x_5364_);
    return v_res_5370_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive(
    mut v_recArgInfo_5371_: *mut crate::leanh::LeanObject,
    mut v_value_5372_: *mut crate::leanh::LeanObject,
    mut v_funType_5373_: *mut crate::leanh::LeanObject,
    mut v_a_5374_: *mut crate::leanh::LeanObject,
    mut v_a_5375_: *mut crate::leanh::LeanObject,
    mut v_a_5376_: *mut crate::leanh::LeanObject,
    mut v_a_5377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5379_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Structural_mkIndPredBRecOnMotive___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    crate::leanh::lean_closure_set(v___f_5379_, 0, v_funType_5373_);
    crate::leanh::lean_closure_set(v___f_5379_, 1, v_recArgInfo_5371_);
    v___x_5380_ = 0;
    v___x_5381_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_value_5372_, v___f_5379_, v___x_5380_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_);
    return v___x_5381_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive___boxed(
    mut v_recArgInfo_5382_: *mut crate::leanh::LeanObject,
    mut v_value_5383_: *mut crate::leanh::LeanObject,
    mut v_funType_5384_: *mut crate::leanh::LeanObject,
    mut v_a_5385_: *mut crate::leanh::LeanObject,
    mut v_a_5386_: *mut crate::leanh::LeanObject,
    mut v_a_5387_: *mut crate::leanh::LeanObject,
    mut v_a_5388_: *mut crate::leanh::LeanObject,
    mut v_a_5389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5390_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(
        v_recArgInfo_5382_,
        v_value_5383_,
        v_funType_5384_,
        v_a_5385_,
        v_a_5386_,
        v_a_5387_,
        v_a_5388_,
    );
    crate::leanh::lean_dec(v_a_5388_);
    crate::leanh::lean_dec_ref(v_a_5387_);
    crate::leanh::lean_dec(v_a_5386_);
    crate::leanh::lean_dec_ref(v_a_5385_);
    return v_res_5390_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v_auxDeclNGen_5392_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5406_: u8 = 0;
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5413_: u8 = 0;
    let mut v_unused_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5395_ = lean_st_ref_take(v___y_5391_);
                v_env_5396_ = crate::leanh::lean_ctor_get(v___x_5395_, 0);
                v_nextMacroScope_5397_ = crate::leanh::lean_ctor_get(v___x_5395_, 1);
                v_ngen_5398_ = crate::leanh::lean_ctor_get(v___x_5395_, 2);
                v_traceState_5399_ = crate::leanh::lean_ctor_get(v___x_5395_, 4);
                v_cache_5400_ = crate::leanh::lean_ctor_get(v___x_5395_, 5);
                v_messages_5401_ = crate::leanh::lean_ctor_get(v___x_5395_, 6);
                v_infoState_5402_ = crate::leanh::lean_ctor_get(v___x_5395_, 7);
                v_snapshotTasks_5403_ = crate::leanh::lean_ctor_get(v___x_5395_, 8);
                v_isSharedCheck_5413_ = (!crate::leanh::lean_is_exclusive(v___x_5395_)) as u8;
                if v_isSharedCheck_5413_ == 0 {
                    v_unused_5414_ = crate::leanh::lean_ctor_get(v___x_5395_, 3);
                    crate::leanh::lean_dec(v_unused_5414_);
                    v___x_5405_ = v___x_5395_;
                    v_isShared_5406_ = v_isSharedCheck_5413_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5403_);
                    crate::leanh::lean_inc(v_infoState_5402_);
                    crate::leanh::lean_inc(v_messages_5401_);
                    crate::leanh::lean_inc(v_cache_5400_);
                    crate::leanh::lean_inc(v_traceState_5399_);
                    crate::leanh::lean_inc(v_ngen_5398_);
                    crate::leanh::lean_inc(v_nextMacroScope_5397_);
                    crate::leanh::lean_inc(v_env_5396_);
                    crate::leanh::lean_dec(v___x_5395_);
                    v___x_5405_ = crate::leanh::lean_box(0);
                    v_isShared_5406_ = v_isSharedCheck_5413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5406_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5405_, 3, v_auxDeclNGen_5392_);
                    v___x_5408_ = v___x_5405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5412_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_env_5396_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 1, v_nextMacroScope_5397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 2, v_ngen_5398_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 3, v_auxDeclNGen_5392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 4, v_traceState_5399_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 5, v_cache_5400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 6, v_messages_5401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 7, v_infoState_5402_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5412_, 8, v_snapshotTasks_5403_);
                    v___x_5408_ = v_reuseFailAlloc_5412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5409_ = lean_st_ref_set(v___y_5391_, v___x_5408_);
                v___x_5410_ = crate::leanh::lean_box(0);
                v___x_5411_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5411_, 0, v___x_5410_);
                return v___x_5411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0___boxed(
    mut v___y_5415_: *mut crate::leanh::LeanObject,
    mut v_auxDeclNGen_5416_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_5417_: *mut crate::leanh::LeanObject,
    mut v___y_5418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5419_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(v___y_5415_, v_auxDeclNGen_5416_, v_a_x3f_5417_);
    crate::leanh::lean_dec(v_a_x3f_5417_);
    crate::leanh::lean_dec(v___y_5415_);
    return v_res_5419_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(
    mut v_name_5420_: *mut crate::leanh::LeanObject,
    mut v_x_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
    mut v___y_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5460_: u8 = 0;
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5464_: u8 = 0;
    let mut v_unused_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v_a_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5473_: u8 = 0;
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut v_unused_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5480_: u8 = 0;
    let mut v_unused_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5428_ = lean_st_ref_get(v___y_5426_);
                v_auxDeclNGen_5429_ = crate::leanh::lean_ctor_get(v___x_5428_, 3);
                crate::leanh::lean_inc_ref(v_auxDeclNGen_5429_);
                crate::leanh::lean_dec(v___x_5428_);
                v_namePrefix_5430_ = crate::leanh::lean_ctor_get(v_auxDeclNGen_5429_, 0);
                v___x_5431_ = lean_name_eq(v_namePrefix_5430_, v_name_5420_);
                if v___x_5431_ == 0 {
                    v___x_5432_ = lean_st_ref_take(v___y_5426_);
                    v_env_5433_ = crate::leanh::lean_ctor_get(v___x_5432_, 0);
                    v_nextMacroScope_5434_ = crate::leanh::lean_ctor_get(v___x_5432_, 1);
                    v_ngen_5435_ = crate::leanh::lean_ctor_get(v___x_5432_, 2);
                    v_traceState_5436_ = crate::leanh::lean_ctor_get(v___x_5432_, 4);
                    v_cache_5437_ = crate::leanh::lean_ctor_get(v___x_5432_, 5);
                    v_messages_5438_ = crate::leanh::lean_ctor_get(v___x_5432_, 6);
                    v_infoState_5439_ = crate::leanh::lean_ctor_get(v___x_5432_, 7);
                    v_snapshotTasks_5440_ = crate::leanh::lean_ctor_get(v___x_5432_, 8);
                    v_isSharedCheck_5480_ = (!crate::leanh::lean_is_exclusive(v___x_5432_)) as u8;
                    if v_isSharedCheck_5480_ == 0 {
                        v_unused_5481_ = crate::leanh::lean_ctor_get(v___x_5432_, 3);
                        crate::leanh::lean_dec(v_unused_5481_);
                        v___x_5442_ = v___x_5432_;
                        v_isShared_5443_ = v_isSharedCheck_5480_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_5440_);
                        crate::leanh::lean_inc(v_infoState_5439_);
                        crate::leanh::lean_inc(v_messages_5438_);
                        crate::leanh::lean_inc(v_cache_5437_);
                        crate::leanh::lean_inc(v_traceState_5436_);
                        crate::leanh::lean_inc(v_ngen_5435_);
                        crate::leanh::lean_inc(v_nextMacroScope_5434_);
                        crate::leanh::lean_inc(v_env_5433_);
                        crate::leanh::lean_dec(v___x_5432_);
                        v___x_5442_ = crate::leanh::lean_box(0);
                        v_isShared_5443_ = v_isSharedCheck_5480_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_auxDeclNGen_5429_);
                    crate::leanh::lean_dec(v_name_5420_);
                    crate::leanh::lean_inc(v___y_5426_);
                    crate::leanh::lean_inc_ref(v___y_5425_);
                    crate::leanh::lean_inc(v___y_5424_);
                    crate::leanh::lean_inc_ref(v___y_5423_);
                    crate::leanh::lean_inc(v___y_5422_);
                    v___x_5482_ = crate::leanh::lean_apply_6(
                        v_x_5421_,
                        v___y_5422_,
                        v___y_5423_,
                        v___y_5424_,
                        v___y_5425_,
                        v___y_5426_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5482_;
                }
            }
            1 => {
                v___x_5444_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5445_ = crate::leanh::lean_box(0);
                v___x_5446_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5446_, 0, v_name_5420_);
                crate::leanh::lean_ctor_set(v___x_5446_, 1, v___x_5444_);
                crate::leanh::lean_ctor_set(v___x_5446_, 2, v___x_5445_);
                if v_isShared_5443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5442_, 3, v___x_5446_);
                    v___x_5448_ = v___x_5442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5479_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_env_5433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 1, v_nextMacroScope_5434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 2, v_ngen_5435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 3, v___x_5446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 4, v_traceState_5436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 5, v_cache_5437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 6, v_messages_5438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 7, v_infoState_5439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5479_, 8, v_snapshotTasks_5440_);
                    v___x_5448_ = v_reuseFailAlloc_5479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5449_ = lean_st_ref_set(v___y_5426_, v___x_5448_);
                crate::leanh::lean_inc(v___y_5426_);
                crate::leanh::lean_inc_ref(v___y_5425_);
                crate::leanh::lean_inc(v___y_5424_);
                crate::leanh::lean_inc_ref(v___y_5423_);
                crate::leanh::lean_inc(v___y_5422_);
                v___x_5450_ = crate::leanh::lean_apply_6(
                    v_x_5421_,
                    v___y_5422_,
                    v___y_5423_,
                    v___y_5424_,
                    v___y_5425_,
                    v___y_5426_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_5450_) == 0 {
                    v_a_5451_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
                    v_isSharedCheck_5467_ = (!crate::leanh::lean_is_exclusive(v___x_5450_)) as u8;
                    if v_isSharedCheck_5467_ == 0 {
                        v___x_5453_ = v___x_5450_;
                        v_isShared_5454_ = v_isSharedCheck_5467_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5451_);
                        crate::leanh::lean_dec(v___x_5450_);
                        v___x_5453_ = crate::leanh::lean_box(0);
                        v_isShared_5454_ = v_isSharedCheck_5467_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5468_ = crate::leanh::lean_ctor_get(v___x_5450_, 0);
                    crate::leanh::lean_inc(v_a_5468_);
                    crate::leanh::lean_dec_ref_known(v___x_5450_, 1);
                    v___x_5469_ = crate::leanh::lean_box(0);
                    v___x_5470_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(v___y_5426_, v_auxDeclNGen_5429_, v___x_5469_);
                    v_isSharedCheck_5477_ = (!crate::leanh::lean_is_exclusive(v___x_5470_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v_unused_5478_ = crate::leanh::lean_ctor_get(v___x_5470_, 0);
                        crate::leanh::lean_dec(v_unused_5478_);
                        v___x_5472_ = v___x_5470_;
                        v_isShared_5473_ = v_isSharedCheck_5477_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5470_);
                        v___x_5472_ = crate::leanh::lean_box(0);
                        v_isShared_5473_ = v_isSharedCheck_5477_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_5451_);
                if v_isShared_5454_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5453_, 1);
                    v___x_5456_ = v___x_5453_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5451_);
                    v___x_5456_ = v_reuseFailAlloc_5466_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5457_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(v___y_5426_, v_auxDeclNGen_5429_, v___x_5456_);
                crate::leanh::lean_dec_ref(v___x_5456_);
                v_isSharedCheck_5464_ = (!crate::leanh::lean_is_exclusive(v___x_5457_)) as u8;
                if v_isSharedCheck_5464_ == 0 {
                    v_unused_5465_ = crate::leanh::lean_ctor_get(v___x_5457_, 0);
                    crate::leanh::lean_dec(v_unused_5465_);
                    v___x_5459_ = v___x_5457_;
                    v_isShared_5460_ = v_isSharedCheck_5464_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5457_);
                    v___x_5459_ = crate::leanh::lean_box(0);
                    v_isShared_5460_ = v_isSharedCheck_5464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5459_, 0, v_a_5451_);
                    v___x_5462_ = v___x_5459_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5463_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5451_);
                    v___x_5462_ = v_reuseFailAlloc_5463_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5462_;
            }
            7 => {
                if v_isShared_5473_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5472_, 1);
                    crate::leanh::lean_ctor_set(v___x_5472_, 0, v_a_5468_);
                    v___x_5475_ = v___x_5472_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5468_);
                    v___x_5475_ = v_reuseFailAlloc_5476_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___boxed(
    mut v_name_5483_: *mut crate::leanh::LeanObject,
    mut v_x_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
    mut v___y_5489_: *mut crate::leanh::LeanObject,
    mut v___y_5490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5491_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(v_name_5483_, v_x_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
    crate::leanh::lean_dec(v___y_5489_);
    crate::leanh::lean_dec_ref(v___y_5488_);
    crate::leanh::lean_dec(v___y_5487_);
    crate::leanh::lean_dec_ref(v___y_5486_);
    crate::leanh::lean_dec(v___y_5485_);
    return v_res_5491_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0(
    mut v_00_u03b1_5492_: *mut crate::leanh::LeanObject,
    mut v_name_5493_: *mut crate::leanh::LeanObject,
    mut v_x_5494_: *mut crate::leanh::LeanObject,
    mut v___y_5495_: *mut crate::leanh::LeanObject,
    mut v___y_5496_: *mut crate::leanh::LeanObject,
    mut v___y_5497_: *mut crate::leanh::LeanObject,
    mut v___y_5498_: *mut crate::leanh::LeanObject,
    mut v___y_5499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5501_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(v_name_5493_, v_x_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_);
    return v___x_5501_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___boxed(
    mut v_00_u03b1_5502_: *mut crate::leanh::LeanObject,
    mut v_name_5503_: *mut crate::leanh::LeanObject,
    mut v_x_5504_: *mut crate::leanh::LeanObject,
    mut v___y_5505_: *mut crate::leanh::LeanObject,
    mut v___y_5506_: *mut crate::leanh::LeanObject,
    mut v___y_5507_: *mut crate::leanh::LeanObject,
    mut v___y_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
    mut v___y_5510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5511_ =
        l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0(
            v_00_u03b1_5502_,
            v_name_5503_,
            v_x_5504_,
            v___y_5505_,
            v___y_5506_,
            v___y_5507_,
            v___y_5508_,
            v___y_5509_,
        );
    crate::leanh::lean_dec(v___y_5509_);
    crate::leanh::lean_dec_ref(v___y_5508_);
    crate::leanh::lean_dec(v___y_5507_);
    crate::leanh::lean_dec_ref(v___y_5506_);
    crate::leanh::lean_dec(v___y_5505_);
    return v_res_5511_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(
    mut v_type_5512_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_5513_: *mut crate::leanh::LeanObject,
    mut v_k_5514_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5515_: u8,
    mut v_whnfType_5516_: u8,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
    mut v___y_5519_: *mut crate::leanh::LeanObject,
    mut v___y_5520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5527_: u8 = 0;
    let mut v___x_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_a_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5522_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_5522_, 0, v_k_5514_);
                v___x_5523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_5512_,
                    v_maxFVars_x3f_5513_,
                    v___f_5522_,
                    v_cleanupAnnotations_5515_,
                    v_whnfType_5516_,
                    v___y_5517_,
                    v___y_5518_,
                    v___y_5519_,
                    v___y_5520_,
                );
                if crate::leanh::lean_obj_tag(v___x_5523_) == 0 {
                    v_a_5524_ = crate::leanh::lean_ctor_get(v___x_5523_, 0);
                    v_isSharedCheck_5531_ = (!crate::leanh::lean_is_exclusive(v___x_5523_)) as u8;
                    if v_isSharedCheck_5531_ == 0 {
                        v___x_5526_ = v___x_5523_;
                        v_isShared_5527_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5524_);
                        crate::leanh::lean_dec(v___x_5523_);
                        v___x_5526_ = crate::leanh::lean_box(0);
                        v_isShared_5527_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5532_ = crate::leanh::lean_ctor_get(v___x_5523_, 0);
                    v_isSharedCheck_5539_ = (!crate::leanh::lean_is_exclusive(v___x_5523_)) as u8;
                    if v_isSharedCheck_5539_ == 0 {
                        v___x_5534_ = v___x_5523_;
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5532_);
                        crate::leanh::lean_dec(v___x_5523_);
                        v___x_5534_ = crate::leanh::lean_box(0);
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5527_ == 0 {
                    v___x_5529_ = v___x_5526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
                    v___x_5529_ = v_reuseFailAlloc_5530_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5529_;
            }
            3 => {
                if v_isShared_5535_ == 0 {
                    v___x_5537_ = v___x_5534_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
                    v___x_5537_ = v_reuseFailAlloc_5538_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5537_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg___boxed(
    mut v_type_5540_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_5541_: *mut crate::leanh::LeanObject,
    mut v_k_5542_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5543_: *mut crate::leanh::LeanObject,
    mut v_whnfType_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5550_: u8 = 0;
    let mut v_whnfType_boxed_5551_: u8 = 0;
    let mut v_res_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5550_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_5543_) as u8);
    v_whnfType_boxed_5551_ = (crate::leanh::lean_unbox(v_whnfType_5544_) as u8);
    v_res_5552_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(v_type_5540_, v_maxFVars_x3f_5541_, v_k_5542_, v_cleanupAnnotations_boxed_5550_, v_whnfType_boxed_5551_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_);
    crate::leanh::lean_dec(v___y_5548_);
    crate::leanh::lean_dec_ref(v___y_5547_);
    crate::leanh::lean_dec(v___y_5546_);
    crate::leanh::lean_dec_ref(v___y_5545_);
    return v_res_5552_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1(
    mut v_00_u03b1_5553_: *mut crate::leanh::LeanObject,
    mut v_type_5554_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_5555_: *mut crate::leanh::LeanObject,
    mut v_k_5556_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5557_: u8,
    mut v_whnfType_5558_: u8,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5564_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(v_type_5554_, v_maxFVars_x3f_5555_, v_k_5556_, v_cleanupAnnotations_5557_, v_whnfType_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
    return v___x_5564_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___boxed(
    mut v_00_u03b1_5565_: *mut crate::leanh::LeanObject,
    mut v_type_5566_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_5567_: *mut crate::leanh::LeanObject,
    mut v_k_5568_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_5569_: *mut crate::leanh::LeanObject,
    mut v_whnfType_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
    mut v___y_5572_: *mut crate::leanh::LeanObject,
    mut v___y_5573_: *mut crate::leanh::LeanObject,
    mut v___y_5574_: *mut crate::leanh::LeanObject,
    mut v___y_5575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_5576_: u8 = 0;
    let mut v_whnfType_boxed_5577_: u8 = 0;
    let mut v_res_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5576_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_5569_) as u8);
    v_whnfType_boxed_5577_ = (crate::leanh::lean_unbox(v_whnfType_5570_) as u8);
    v_res_5578_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1(
            v_00_u03b1_5565_,
            v_type_5566_,
            v_maxFVars_x3f_5567_,
            v_k_5568_,
            v_cleanupAnnotations_boxed_5576_,
            v_whnfType_boxed_5577_,
            v___y_5571_,
            v___y_5572_,
            v___y_5573_,
            v___y_5574_,
        );
    crate::leanh::lean_dec(v___y_5574_);
    crate::leanh::lean_dec_ref(v___y_5573_);
    crate::leanh::lean_dec(v___y_5572_);
    crate::leanh::lean_dec_ref(v___y_5571_);
    return v_res_5578_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0(
    mut v___x_5581_: *mut crate::leanh::LeanObject,
    mut v_recArgInfo_5582_: *mut crate::leanh::LeanObject,
    mut v_fst_5583_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_5584_: *mut crate::leanh::LeanObject,
    mut v_positions_5585_: *mut crate::leanh::LeanObject,
    mut v_params_5586_: *mut crate::leanh::LeanObject,
    mut v_value_5587_: *mut crate::leanh::LeanObject,
    mut v_snd_5588_: *mut crate::leanh::LeanObject,
    mut v_below_5589_: *mut crate::leanh::LeanObject,
    mut v_x_5590_: *mut crate::leanh::LeanObject,
    mut v___y_5591_: *mut crate::leanh::LeanObject,
    mut v___y_5592_: *mut crate::leanh::LeanObject,
    mut v___y_5593_: *mut crate::leanh::LeanObject,
    mut v___y_5594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnName_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: u8 = 0;
    let mut v___x_5624_: u8 = 0;
    let mut v___x_5625_: u8 = 0;
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5630_: u8 = 0;
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5643_: u8 = 0;
    let mut v_a_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5647_: u8 = 0;
    let mut v___x_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v_a_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5655_: u8 = 0;
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5596_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5597_ = lean_array_get_borrowed(v___x_5581_, v_below_5589_, v___x_5596_);
                crate::leanh::lean_inc(v___y_5594_);
                crate::leanh::lean_inc_ref(v___y_5593_);
                crate::leanh::lean_inc(v___y_5592_);
                crate::leanh::lean_inc_ref(v___y_5591_);
                crate::leanh::lean_inc(v___x_5597_);
                v___x_5598_ = lean_infer_type(
                    v___x_5597_,
                    v___y_5591_,
                    v___y_5592_,
                    v___y_5593_,
                    v___y_5594_,
                );
                if crate::leanh::lean_obj_tag(v___x_5598_) == 0 {
                    v_a_5599_ = crate::leanh::lean_ctor_get(v___x_5598_, 0);
                    crate::leanh::lean_inc(v_a_5599_);
                    crate::leanh::lean_dec_ref_known(v___x_5598_, 1);
                    v___x_5600_ = l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0;
                    v___x_5601_ = lean_st_mk_ref(v___x_5600_);
                    v_fnName_5602_ = crate::leanh::lean_ctor_get(v_recArgInfo_5582_, 0);
                    crate::leanh::lean_inc(v_fnName_5602_);
                    crate::leanh::lean_dec_ref(v_recArgInfo_5582_);
                    v___x_5603_ = crate::leanh::lean_box(1);
                    v___x_5604_ = l_Lean_Expr_getForallBody(v_a_5599_);
                    crate::leanh::lean_dec(v_a_5599_);
                    v___x_5605_ = l_Lean_Expr_getAppFn(v___x_5604_);
                    crate::leanh::lean_dec_ref(v___x_5604_);
                    v___x_5606_ = l_Lean_Expr_constName_x21(v___x_5605_);
                    crate::leanh::lean_dec_ref(v___x_5605_);
                    v___x_5607_ = lean_array_get_size(v_fst_5583_);
                    v___x_5608_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5609_ = lean_nat_sub(v___x_5607_, v___x_5608_);
                    v___x_5610_ = lean_array_get_borrowed(v___x_5581_, v_fst_5583_, v___x_5609_);
                    crate::leanh::lean_dec(v___x_5609_);
                    v___x_5611_ = l_Lean_Expr_fvarId_x21(v___x_5610_);
                    crate::leanh::lean_inc(v___x_5597_);
                    v___x_5612_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5612_, 0, v___x_5606_);
                    crate::leanh::lean_ctor_set(v___x_5612_, 1, v___x_5597_);
                    v___x_5613_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_5611_, v___x_5612_, v___x_5603_);
                    v___x_5614_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5614_, 0, v___x_5613_);
                    crate::leanh::lean_ctor_set(v___x_5614_, 1, v___x_5603_);
                    v___x_5615_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___boxed as *mut core::ffi::c_void, 11, 5);
                    crate::leanh::lean_closure_set(v___x_5615_, 0, v_recArgInfos_5584_);
                    crate::leanh::lean_closure_set(v___x_5615_, 1, v_positions_5585_);
                    crate::leanh::lean_closure_set(v___x_5615_, 2, v_params_5586_);
                    crate::leanh::lean_closure_set(v___x_5615_, 3, v___x_5614_);
                    crate::leanh::lean_closure_set(v___x_5615_, 4, v_value_5587_);
                    v___x_5616_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(v_fnName_5602_, v___x_5615_, v___x_5601_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
                    if crate::leanh::lean_obj_tag(v___x_5616_) == 0 {
                        v_a_5617_ = crate::leanh::lean_ctor_get(v___x_5616_, 0);
                        crate::leanh::lean_inc(v_a_5617_);
                        crate::leanh::lean_dec_ref_known(v___x_5616_, 1);
                        v___x_5618_ = lean_st_ref_get(v___x_5601_);
                        crate::leanh::lean_dec(v___x_5601_);
                        v___x_5619_ = lean_mk_empty_array_with_capacity(v___x_5608_);
                        crate::leanh::lean_inc(v___x_5597_);
                        v___x_5620_ = lean_array_push(v___x_5619_, v___x_5597_);
                        v___x_5621_ = l_Array_append___redArg(v_fst_5583_, v___x_5620_);
                        crate::leanh::lean_dec_ref(v___x_5620_);
                        v___x_5622_ = l_Array_append___redArg(v___x_5621_, v_snd_5588_);
                        v___x_5623_ = 0;
                        v___x_5624_ = 1;
                        v___x_5625_ = 1;
                        v___x_5626_ = l_Lean_Meta_mkLambdaFVars(
                            v___x_5622_,
                            v_a_5617_,
                            v___x_5623_,
                            v___x_5624_,
                            v___x_5623_,
                            v___x_5624_,
                            v___x_5625_,
                            v___y_5591_,
                            v___y_5592_,
                            v___y_5593_,
                            v___y_5594_,
                        );
                        crate::leanh::lean_dec_ref(v___x_5622_);
                        if crate::leanh::lean_obj_tag(v___x_5626_) == 0 {
                            v_a_5627_ = crate::leanh::lean_ctor_get(v___x_5626_, 0);
                            v_isSharedCheck_5635_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5626_)) as u8;
                            if v_isSharedCheck_5635_ == 0 {
                                v___x_5629_ = v___x_5626_;
                                v_isShared_5630_ = v_isSharedCheck_5635_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5627_);
                                crate::leanh::lean_dec(v___x_5626_);
                                v___x_5629_ = crate::leanh::lean_box(0);
                                v_isShared_5630_ = v_isSharedCheck_5635_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_5618_);
                            v_a_5636_ = crate::leanh::lean_ctor_get(v___x_5626_, 0);
                            v_isSharedCheck_5643_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5626_)) as u8;
                            if v_isSharedCheck_5643_ == 0 {
                                v___x_5638_ = v___x_5626_;
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5636_);
                                crate::leanh::lean_dec(v___x_5626_);
                                v___x_5638_ = crate::leanh::lean_box(0);
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5601_);
                        crate::leanh::lean_dec_ref(v_fst_5583_);
                        v_a_5644_ = crate::leanh::lean_ctor_get(v___x_5616_, 0);
                        v_isSharedCheck_5651_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5616_)) as u8;
                        if v_isSharedCheck_5651_ == 0 {
                            v___x_5646_ = v___x_5616_;
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5644_);
                            crate::leanh::lean_dec(v___x_5616_);
                            v___x_5646_ = crate::leanh::lean_box(0);
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_5587_);
                    crate::leanh::lean_dec_ref(v_params_5586_);
                    crate::leanh::lean_dec_ref(v_positions_5585_);
                    crate::leanh::lean_dec_ref(v_recArgInfos_5584_);
                    crate::leanh::lean_dec_ref(v_fst_5583_);
                    crate::leanh::lean_dec_ref(v_recArgInfo_5582_);
                    v_a_5652_ = crate::leanh::lean_ctor_get(v___x_5598_, 0);
                    v_isSharedCheck_5659_ = (!crate::leanh::lean_is_exclusive(v___x_5598_)) as u8;
                    if v_isSharedCheck_5659_ == 0 {
                        v___x_5654_ = v___x_5598_;
                        v_isShared_5655_ = v_isSharedCheck_5659_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5652_);
                        crate::leanh::lean_dec(v___x_5598_);
                        v___x_5654_ = crate::leanh::lean_box(0);
                        v_isShared_5655_ = v_isSharedCheck_5659_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5631_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5631_, 0, v_a_5627_);
                crate::leanh::lean_ctor_set(v___x_5631_, 1, v___x_5618_);
                if v_isShared_5630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5629_, 0, v___x_5631_);
                    v___x_5633_ = v___x_5629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5634_, 0, v___x_5631_);
                    v___x_5633_ = v_reuseFailAlloc_5634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5633_;
            }
            3 => {
                if v_isShared_5639_ == 0 {
                    v___x_5641_ = v___x_5638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_a_5636_);
                    v___x_5641_ = v_reuseFailAlloc_5642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5641_;
            }
            5 => {
                if v_isShared_5647_ == 0 {
                    v___x_5649_ = v___x_5646_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_a_5644_);
                    v___x_5649_ = v_reuseFailAlloc_5650_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5649_;
            }
            7 => {
                if v_isShared_5655_ == 0 {
                    v___x_5657_ = v___x_5654_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5658_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_a_5652_);
                    v___x_5657_ = v_reuseFailAlloc_5658_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5657_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___boxed(
    mut v___x_5660_: *mut crate::leanh::LeanObject,
    mut v_recArgInfo_5661_: *mut crate::leanh::LeanObject,
    mut v_fst_5662_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_5663_: *mut crate::leanh::LeanObject,
    mut v_positions_5664_: *mut crate::leanh::LeanObject,
    mut v_params_5665_: *mut crate::leanh::LeanObject,
    mut v_value_5666_: *mut crate::leanh::LeanObject,
    mut v_snd_5667_: *mut crate::leanh::LeanObject,
    mut v_below_5668_: *mut crate::leanh::LeanObject,
    mut v_x_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
    mut v___y_5674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5675_ = l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0(
        v___x_5660_,
        v_recArgInfo_5661_,
        v_fst_5662_,
        v_recArgInfos_5663_,
        v_positions_5664_,
        v_params_5665_,
        v_value_5666_,
        v_snd_5667_,
        v_below_5668_,
        v_x_5669_,
        v___y_5670_,
        v___y_5671_,
        v___y_5672_,
        v___y_5673_,
    );
    crate::leanh::lean_dec(v___y_5673_);
    crate::leanh::lean_dec_ref(v___y_5672_);
    crate::leanh::lean_dec(v___y_5671_);
    crate::leanh::lean_dec_ref(v___y_5670_);
    crate::leanh::lean_dec_ref(v_x_5669_);
    crate::leanh::lean_dec_ref(v_below_5668_);
    crate::leanh::lean_dec_ref(v_snd_5667_);
    crate::leanh::lean_dec_ref(v___x_5660_);
    return v_res_5675_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1(
    mut v_recArgInfo_5678_: *mut crate::leanh::LeanObject,
    mut v_FType_5679_: *mut crate::leanh::LeanObject,
    mut v___x_5680_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_5681_: *mut crate::leanh::LeanObject,
    mut v_positions_5682_: *mut crate::leanh::LeanObject,
    mut v_params_5683_: *mut crate::leanh::LeanObject,
    mut v_xs_5684_: *mut crate::leanh::LeanObject,
    mut v_value_5685_: *mut crate::leanh::LeanObject,
    mut v___y_5686_: *mut crate::leanh::LeanObject,
    mut v___y_5687_: *mut crate::leanh::LeanObject,
    mut v___y_5688_: *mut crate::leanh::LeanObject,
    mut v___y_5689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: u8 = 0;
    let mut v___x_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5703_: u8 = 0;
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_recArgInfo_5678_);
                v___x_5691_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(
                    v_recArgInfo_5678_,
                    v_xs_5684_,
                );
                v_fst_5692_ = crate::leanh::lean_ctor_get(v___x_5691_, 0);
                crate::leanh::lean_inc(v_fst_5692_);
                v_snd_5693_ = crate::leanh::lean_ctor_get(v___x_5691_, 1);
                crate::leanh::lean_inc(v_snd_5693_);
                crate::leanh::lean_dec_ref(v___x_5691_);
                v___x_5694_ = l_Lean_Meta_instantiateForall(
                    v_FType_5679_,
                    v_fst_5692_,
                    v___y_5686_,
                    v___y_5687_,
                    v___y_5688_,
                    v___y_5689_,
                );
                if crate::leanh::lean_obj_tag(v___x_5694_) == 0 {
                    v_a_5695_ = crate::leanh::lean_ctor_get(v___x_5694_, 0);
                    crate::leanh::lean_inc(v_a_5695_);
                    crate::leanh::lean_dec_ref_known(v___x_5694_, 1);
                    v___f_5696_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___boxed
                            as *mut core::ffi::c_void,
                        15,
                        8,
                    );
                    crate::leanh::lean_closure_set(v___f_5696_, 0, v___x_5680_);
                    crate::leanh::lean_closure_set(v___f_5696_, 1, v_recArgInfo_5678_);
                    crate::leanh::lean_closure_set(v___f_5696_, 2, v_fst_5692_);
                    crate::leanh::lean_closure_set(v___f_5696_, 3, v_recArgInfos_5681_);
                    crate::leanh::lean_closure_set(v___f_5696_, 4, v_positions_5682_);
                    crate::leanh::lean_closure_set(v___f_5696_, 5, v_params_5683_);
                    crate::leanh::lean_closure_set(v___f_5696_, 6, v_value_5685_);
                    crate::leanh::lean_closure_set(v___f_5696_, 7, v_snd_5693_);
                    v___x_5697_ = l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0;
                    v___x_5698_ = 0;
                    v___x_5699_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(v_a_5695_, v___x_5697_, v___f_5696_, v___x_5698_, v___x_5698_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
                    return v___x_5699_;
                } else {
                    crate::leanh::lean_dec(v_snd_5693_);
                    crate::leanh::lean_dec(v_fst_5692_);
                    crate::leanh::lean_dec_ref(v_value_5685_);
                    crate::leanh::lean_dec_ref(v_params_5683_);
                    crate::leanh::lean_dec_ref(v_positions_5682_);
                    crate::leanh::lean_dec_ref(v_recArgInfos_5681_);
                    crate::leanh::lean_dec_ref(v___x_5680_);
                    crate::leanh::lean_dec_ref(v_recArgInfo_5678_);
                    v_a_5700_ = crate::leanh::lean_ctor_get(v___x_5694_, 0);
                    v_isSharedCheck_5707_ = (!crate::leanh::lean_is_exclusive(v___x_5694_)) as u8;
                    if v_isSharedCheck_5707_ == 0 {
                        v___x_5702_ = v___x_5694_;
                        v_isShared_5703_ = v_isSharedCheck_5707_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5700_);
                        crate::leanh::lean_dec(v___x_5694_);
                        v___x_5702_ = crate::leanh::lean_box(0);
                        v_isShared_5703_ = v_isSharedCheck_5707_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5703_ == 0 {
                    v___x_5705_ = v___x_5702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5706_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_a_5700_);
                    v___x_5705_ = v_reuseFailAlloc_5706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___boxed(
    mut v_recArgInfo_5708_: *mut crate::leanh::LeanObject,
    mut v_FType_5709_: *mut crate::leanh::LeanObject,
    mut v___x_5710_: *mut crate::leanh::LeanObject,
    mut v_recArgInfos_5711_: *mut crate::leanh::LeanObject,
    mut v_positions_5712_: *mut crate::leanh::LeanObject,
    mut v_params_5713_: *mut crate::leanh::LeanObject,
    mut v_xs_5714_: *mut crate::leanh::LeanObject,
    mut v_value_5715_: *mut crate::leanh::LeanObject,
    mut v___y_5716_: *mut crate::leanh::LeanObject,
    mut v___y_5717_: *mut crate::leanh::LeanObject,
    mut v___y_5718_: *mut crate::leanh::LeanObject,
    mut v___y_5719_: *mut crate::leanh::LeanObject,
    mut v___y_5720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5721_ = l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1(
        v_recArgInfo_5708_,
        v_FType_5709_,
        v___x_5710_,
        v_recArgInfos_5711_,
        v_positions_5712_,
        v_params_5713_,
        v_xs_5714_,
        v_value_5715_,
        v___y_5716_,
        v___y_5717_,
        v___y_5718_,
        v___y_5719_,
    );
    crate::leanh::lean_dec(v___y_5719_);
    crate::leanh::lean_dec_ref(v___y_5718_);
    crate::leanh::lean_dec(v___y_5717_);
    crate::leanh::lean_dec_ref(v___y_5716_);
    return v_res_5721_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF(
    mut v_recArgInfos_5722_: *mut crate::leanh::LeanObject,
    mut v_positions_5723_: *mut crate::leanh::LeanObject,
    mut v_recArgInfo_5724_: *mut crate::leanh::LeanObject,
    mut v_value_5725_: *mut crate::leanh::LeanObject,
    mut v_FType_5726_: *mut crate::leanh::LeanObject,
    mut v_params_5727_: *mut crate::leanh::LeanObject,
    mut v_a_5728_: *mut crate::leanh::LeanObject,
    mut v_a_5729_: *mut crate::leanh::LeanObject,
    mut v_a_5730_: *mut crate::leanh::LeanObject,
    mut v_a_5731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u8 = 0;
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5733_ = l_Lean_instInhabitedExpr;
    v___f_5734_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___boxed as *mut core::ffi::c_void,
        13,
        6,
    );
    crate::leanh::lean_closure_set(v___f_5734_, 0, v_recArgInfo_5724_);
    crate::leanh::lean_closure_set(v___f_5734_, 1, v_FType_5726_);
    crate::leanh::lean_closure_set(v___f_5734_, 2, v___x_5733_);
    crate::leanh::lean_closure_set(v___f_5734_, 3, v_recArgInfos_5722_);
    crate::leanh::lean_closure_set(v___f_5734_, 4, v_positions_5723_);
    crate::leanh::lean_closure_set(v___f_5734_, 5, v_params_5727_);
    v___x_5735_ = 0;
    v___x_5736_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_value_5725_, v___f_5734_, v___x_5735_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_);
    return v___x_5736_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed(
    mut v_recArgInfos_5737_: *mut crate::leanh::LeanObject,
    mut v_positions_5738_: *mut crate::leanh::LeanObject,
    mut v_recArgInfo_5739_: *mut crate::leanh::LeanObject,
    mut v_value_5740_: *mut crate::leanh::LeanObject,
    mut v_FType_5741_: *mut crate::leanh::LeanObject,
    mut v_params_5742_: *mut crate::leanh::LeanObject,
    mut v_a_5743_: *mut crate::leanh::LeanObject,
    mut v_a_5744_: *mut crate::leanh::LeanObject,
    mut v_a_5745_: *mut crate::leanh::LeanObject,
    mut v_a_5746_: *mut crate::leanh::LeanObject,
    mut v_a_5747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5748_ = l_Lean_Elab_Structural_mkIndPredBRecOnF(
        v_recArgInfos_5737_,
        v_positions_5738_,
        v_recArgInfo_5739_,
        v_value_5740_,
        v_FType_5741_,
        v_params_5742_,
        v_a_5743_,
        v_a_5744_,
        v_a_5745_,
        v_a_5746_,
    );
    crate::leanh::lean_dec(v_a_5746_);
    crate::leanh::lean_dec_ref(v_a_5745_);
    crate::leanh::lean_dec(v_a_5744_);
    crate::leanh::lean_dec_ref(v_a_5743_);
    return v_res_5748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_HasConstCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IndPredBelow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_IndPred(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_IndPred(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_HasConstCache(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_IndPredBelow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
}
