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
    l_Array_extract___redArg, l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3,
    l_Lean_replaceRef, l_List_lengthTR___redArg,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_6,
    lean_apply_7, lean_apply_8, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [65, 110, 100, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__0_value) as *mut LeanObject,9743492140944907313 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0_value: LeanStringObject<60> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [105, 110, 115, 117, 102, 102, 105, 99, 105, 101, 110, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 97, 116, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 101, 108, 105, 109, 105, 110, 97, 116, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3_value) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__1_value: LeanStringObject<27> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 97, 116, 99, 104, 77, 97, 116, 99, 104, 101, 114, 65, 112, 112, 63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__0_value) as *mut LeanObject,12843180897352504333 as *mut LeanObject] };
static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__1_value) as *mut LeanObject,6897119537390546559 as *mut LeanObject] };
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__2_value) as *mut LeanObject,14406337792964512117 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__4_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [109, 97, 116, 99, 104, 101, 114, 65, 112, 112, 32, 98, 101, 102, 111, 114, 101, 32, 97, 100, 100, 105, 110, 103, 32, 98, 101, 108, 111, 119, 32, 116, 114, 97, 110, 115, 102, 111, 114, 109, 97, 116, 105, 111, 110, 58, 10, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [102, 117, 110, 84, 121, 112, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__0_value) as *mut LeanObject,11438940029995117633 as *mut LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj(
    mut v_i_2878_: *mut LeanObject,
    mut v_n_2879_: *mut LeanObject,
    mut v_e_2880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2882_: u8 = 0;
    let mut v_isZero_2883_: u8 = 0;
    let mut v_one_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2889_: u8 = 0;
    let mut v_one_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2881_ = lean_unsigned_to_nat(0);
                v_isZero_2882_ = lean_nat_dec_eq(v_i_2878_, v_zero_2881_);
                if v_isZero_2882_ == 1 {
                    lean_dec(v_i_2878_);
                    v_isZero_2883_ = lean_nat_dec_eq(v_n_2879_, v_zero_2881_);
                    if v_isZero_2883_ == 0 {
                        v_one_2884_ = lean_unsigned_to_nat(1);
                        v_n_2885_ = lean_nat_sub(v_n_2879_, v_one_2884_);
                        lean_dec(v_n_2879_);
                        v___x_2886_ = lean_nat_dec_eq(v_n_2885_, v_zero_2881_);
                        lean_dec(v_n_2885_);
                        if v___x_2886_ == 0 {
                            v___x_2887_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1;
                            v___x_2888_ =
                                l_Lean_Expr_proj___override(v___x_2887_, v_zero_2881_, v_e_2880_);
                            return v___x_2888_;
                        } else {
                            return v_e_2880_;
                        }
                    } else {
                        lean_dec(v_n_2879_);
                        return v_e_2880_;
                    }
                } else {
                    v_isZero_2889_ = lean_nat_dec_eq(v_n_2879_, v_zero_2881_);
                    if v_isZero_2889_ == 0 {
                        v_one_2890_ = lean_unsigned_to_nat(1);
                        v_n_2891_ = lean_nat_sub(v_i_2878_, v_one_2890_);
                        lean_dec(v_i_2878_);
                        v_n_2892_ = lean_nat_sub(v_n_2879_, v_one_2890_);
                        lean_dec(v_n_2879_);
                        v___x_2893_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj___closed__1;
                        v___x_2894_ =
                            l_Lean_Expr_proj___override(v___x_2893_, v_one_2890_, v_e_2880_);
                        v_i_2878_ = v_n_2891_;
                        v_n_2879_ = v_n_2892_;
                        v_e_2880_ = v___x_2894_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_n_2879_);
                        lean_dec(v_i_2878_);
                        return v_e_2880_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(
    mut v_t_2896_: *mut LeanObject,
    mut v_k_2897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2896_) == 0 {
                    v_k_2898_ = lean_ctor_get(v_t_2896_, 1);
                    v_v_2899_ = lean_ctor_get(v_t_2896_, 2);
                    v_l_2900_ = lean_ctor_get(v_t_2896_, 3);
                    v_r_2901_ = lean_ctor_get(v_t_2896_, 4);
                    v___x_2902_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2897_, v_k_2898_);
                    match v___x_2902_ {
                        0 => {
                            v_t_2896_ = v_l_2900_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_2899_);
                            v___x_2904_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2904_, 0, v_v_2899_);
                            return v___x_2904_;
                        }
                        _ => {
                            v_t_2896_ = v_r_2901_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2906_ = lean_box(0);
                    return v___x_2906_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg___boxed(
    mut v_t_2907_: *mut LeanObject,
    mut v_k_2908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2909_: *mut LeanObject = core::ptr::null_mut();
    v_res_2909_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(v_t_2907_, v_k_2908_);
    lean_dec(v_k_2908_);
    lean_dec(v_t_2907_);
    return v_res_2909_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4(
    mut v_xs_2910_: *mut LeanObject,
    mut v_v_2911_: *mut LeanObject,
    mut v_i_2912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: u8 = 0;
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: u8 = 0;
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2913_ = lean_array_get_size(v_xs_2910_);
                v___x_2914_ = lean_nat_dec_lt(v_i_2912_, v___x_2913_);
                if v___x_2914_ == 0 {
                    lean_dec(v_i_2912_);
                    v___x_2915_ = lean_box(0);
                    return v___x_2915_;
                } else {
                    v___x_2916_ = lean_array_fget_borrowed(v_xs_2910_, v_i_2912_);
                    v___x_2917_ = lean_nat_dec_eq(v___x_2916_, v_v_2911_);
                    if v___x_2917_ == 0 {
                        v___x_2918_ = lean_unsigned_to_nat(1);
                        v___x_2919_ = lean_nat_add(v_i_2912_, v___x_2918_);
                        lean_dec(v_i_2912_);
                        v_i_2912_ = v___x_2919_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2921_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2921_, 0, v_i_2912_);
                        return v___x_2921_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4___boxed(
    mut v_xs_2922_: *mut LeanObject,
    mut v_v_2923_: *mut LeanObject,
    mut v_i_2924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2925_: *mut LeanObject = core::ptr::null_mut();
    v_res_2925_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4(v_xs_2922_, v_v_2923_, v_i_2924_);
    lean_dec(v_v_2923_);
    lean_dec_ref(v_xs_2922_);
    return v_res_2925_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3(
    mut v_xs_2926_: *mut LeanObject,
    mut v_v_2927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    v___x_2928_ = lean_unsigned_to_nat(0);
    v___x_2929_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3_spec__4(v_xs_2926_, v_v_2927_, v___x_2928_);
    return v___x_2929_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3___boxed(
    mut v_xs_2930_: *mut LeanObject,
    mut v_v_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2932_: *mut LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3(v_xs_2930_, v_v_2931_);
    lean_dec(v_v_2931_);
    lean_dec_ref(v_xs_2930_);
    return v_res_2932_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2(
    mut v_xs_2933_: *mut LeanObject,
    mut v_v_2934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2935_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2_spec__3(v_xs_2933_, v_v_2934_);
                if lean_obj_tag(v___x_2935_) == 0 {
                    v___x_2936_ = lean_box(0);
                    return v___x_2936_;
                } else {
                    v_val_2937_ = lean_ctor_get(v___x_2935_, 0);
                    v_isSharedCheck_2944_ = (!lean_is_exclusive(v___x_2935_)) as u8;
                    if v_isSharedCheck_2944_ == 0 {
                        v___x_2939_ = v___x_2935_;
                        v_isShared_2940_ = v_isSharedCheck_2944_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2937_);
                        lean_dec(v___x_2935_);
                        v___x_2939_ = lean_box(0);
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
                    v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_val_2937_);
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
    mut v_xs_2945_: *mut LeanObject,
    mut v_v_2946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2947_: *mut LeanObject = core::ptr::null_mut();
    v_res_2947_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2(v_xs_2945_, v_v_2946_);
    lean_dec(v_v_2946_);
    lean_dec_ref(v_xs_2945_);
    return v_res_2947_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3_spec__5(
    mut v_a_2948_: *mut LeanObject,
    mut v_as_2949_: *mut LeanObject,
    mut v_i_2950_: usize,
    mut v_stop_2951_: usize,
) -> u8 {
    let mut v___x_2952_: u8 = 0;
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_2959_: *mut LeanObject,
    mut v_as_2960_: *mut LeanObject,
    mut v_i_2961_: *mut LeanObject,
    mut v_stop_2962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2963_: usize = 0;
    let mut v_stop_boxed_2964_: usize = 0;
    let mut v_res_2965_: u8 = 0;
    let mut v_r_2966_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2963_ = lean_unbox_usize(v_i_2961_);
    lean_dec(v_i_2961_);
    v_stop_boxed_2964_ = lean_unbox_usize(v_stop_2962_);
    lean_dec(v_stop_2962_);
    v_res_2965_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3_spec__5(v_a_2959_, v_as_2960_, v_i_boxed_2963_, v_stop_boxed_2964_);
    lean_dec_ref(v_as_2960_);
    lean_dec(v_a_2959_);
    v_r_2966_ = lean_box((v_res_2965_) as usize);
    return v_r_2966_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3(
    mut v_as_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
) -> u8 {
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: u8 = 0;
    v___x_2969_ = lean_unsigned_to_nat(0);
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
    mut v_as_2975_: *mut LeanObject,
    mut v_a_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2977_: u8 = 0;
    let mut v_r_2978_: *mut LeanObject = core::ptr::null_mut();
    v_res_2977_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__3(v_as_2975_, v_a_2976_);
    lean_dec(v_a_2976_);
    lean_dec_ref(v_as_2975_);
    v_r_2978_ = lean_box((v_res_2977_) as usize);
    return v_r_2978_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(
    mut v_recArgInfo_2979_: *mut LeanObject,
    mut v_args_2980_: *mut LeanObject,
    mut v_upperBound_2981_: *mut LeanObject,
    mut v___x_2982_: *mut LeanObject,
    mut v_a_2983_: *mut LeanObject,
    mut v_b_2984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fixedParamPerm_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2996_: u8 = 0;
    let mut v___x_2997_: u8 = 0;
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: u8 = 0;
    let mut v___x_3001_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_nat_dec_lt(v_a_2983_, v_upperBound_2981_);
                if v___x_2991_ == 0 {
                    lean_dec(v_a_2983_);
                    v___x_2992_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2992_, 0, v_b_2984_);
                    return v___x_2992_;
                } else {
                    v_fixedParamPerm_2993_ = lean_ctor_get(v_recArgInfo_2979_, 1);
                    v_indicesPos_2994_ = lean_ctor_get(v_recArgInfo_2979_, 3);
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
                v___x_2988_ = lean_unsigned_to_nat(1);
                v___x_2989_ = lean_nat_add(v_a_2983_, v___x_2988_);
                lean_dec(v_a_2983_);
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
                        lean_inc(v___x_2998_);
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
    mut v_recArgInfo_3002_: *mut LeanObject,
    mut v_args_3003_: *mut LeanObject,
    mut v_upperBound_3004_: *mut LeanObject,
    mut v___x_3005_: *mut LeanObject,
    mut v_a_3006_: *mut LeanObject,
    mut v_b_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3009_: *mut LeanObject = core::ptr::null_mut();
    v_res_3009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(v_recArgInfo_3002_, v_args_3003_, v_upperBound_3004_, v___x_3005_, v_a_3006_, v_b_3007_);
    lean_dec(v___x_3005_);
    lean_dec(v_upperBound_3004_);
    lean_dec_ref(v_args_3003_);
    lean_dec_ref(v_recArgInfo_3002_);
    return v_res_3009_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(
    mut v_msgData_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
    mut v___y_3014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    v___x_3016_ = lean_st_ref_get(v___y_3014_);
    v_env_3017_ = lean_ctor_get(v___x_3016_, 0);
    lean_inc_ref(v_env_3017_);
    lean_dec(v___x_3016_);
    v___x_3018_ = lean_st_ref_get(v___y_3012_);
    v_mctx_3019_ = lean_ctor_get(v___x_3018_, 0);
    lean_inc_ref(v_mctx_3019_);
    lean_dec(v___x_3018_);
    v_lctx_3020_ = lean_ctor_get(v___y_3011_, 2);
    v_options_3021_ = lean_ctor_get(v___y_3013_, 2);
    lean_inc_ref(v_options_3021_);
    lean_inc_ref(v_lctx_3020_);
    v___x_3022_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3022_, 0, v_env_3017_);
    lean_ctor_set(v___x_3022_, 1, v_mctx_3019_);
    lean_ctor_set(v___x_3022_, 2, v_lctx_3020_);
    lean_ctor_set(v___x_3022_, 3, v_options_3021_);
    v___x_3023_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3023_, 0, v___x_3022_);
    lean_ctor_set(v___x_3023_, 1, v_msgData_3010_);
    v___x_3024_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3024_, 0, v___x_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0___boxed(
    mut v_msgData_3025_: *mut LeanObject,
    mut v___y_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
    mut v___y_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3031_: *mut LeanObject = core::ptr::null_mut();
    v_res_3031_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msgData_3025_, v___y_3026_, v___y_3027_, v___y_3028_, v___y_3029_);
    lean_dec(v___y_3029_);
    lean_dec_ref(v___y_3028_);
    lean_dec(v___y_3027_);
    lean_dec_ref(v___y_3026_);
    return v_res_3031_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(
    mut v_msg_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
    mut v___y_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3043_: u8 = 0;
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3038_ = lean_ctor_get(v___y_3035_, 5);
                v___x_3039_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msg_3032_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
                v_a_3040_ = lean_ctor_get(v___x_3039_, 0);
                v_isSharedCheck_3048_ = (!lean_is_exclusive(v___x_3039_)) as u8;
                if v_isSharedCheck_3048_ == 0 {
                    v___x_3042_ = v___x_3039_;
                    v_isShared_3043_ = v_isSharedCheck_3048_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3040_);
                    lean_dec(v___x_3039_);
                    v___x_3042_ = lean_box(0);
                    v_isShared_3043_ = v_isSharedCheck_3048_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3038_);
                v___x_3044_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3044_, 0, v_ref_3038_);
                lean_ctor_set(v___x_3044_, 1, v_a_3040_);
                if v_isShared_3043_ == 0 {
                    lean_ctor_set_tag(v___x_3042_, 1);
                    lean_ctor_set(v___x_3042_, 0, v___x_3044_);
                    v___x_3046_ = v___x_3042_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
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
    mut v_msg_3049_: *mut LeanObject,
    mut v___y_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
    mut v___y_3053_: *mut LeanObject,
    mut v___y_3054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3055_: *mut LeanObject = core::ptr::null_mut();
    v_res_3055_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v_msg_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
    lean_dec(v___y_3053_);
    lean_dec_ref(v___y_3052_);
    lean_dec(v___y_3051_);
    lean_dec_ref(v___y_3050_);
    return v_res_3055_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1()
-> *mut LeanObject {
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    v___x_3057_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__0;
    v___x_3058_ = l_Lean_stringToMessageData(v___x_3057_);
    return v___x_3058_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3()
-> *mut LeanObject {
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    v___x_3060_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__2;
    v___x_3061_ = l_Lean_stringToMessageData(v___x_3060_);
    return v___x_3061_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4()
-> *mut LeanObject {
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    v___x_3062_ = l_Array_instInhabited(lean_box(0));
    return v___x_3062_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6()
-> *mut LeanObject {
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3066_: *mut LeanObject = core::ptr::null_mut();
    v___x_3065_ = lean_box(0);
    v_dummy_3066_ = l_Lean_Expr_sort___override(v___x_3065_);
    return v_dummy_3066_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp(
    mut v_recArgInfo_3067_: *mut LeanObject,
    mut v_ctx_3068_: *mut LeanObject,
    mut v_fidx_3069_: *mut LeanObject,
    mut v_positions_3070_: *mut LeanObject,
    mut v_e_3071_: *mut LeanObject,
    mut v_args_3072_: *mut LeanObject,
    mut v_a_3073_: *mut LeanObject,
    mut v_a_3074_: *mut LeanObject,
    mut v_a_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_recArgPos_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: u8 = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motives_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3114_: u8 = 0;
    let mut v_nargs_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3128_: u8 = 0;
    let mut v_a_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3132_: u8 = 0;
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_recArgPos_3078_ = lean_ctor_get(v_recArgInfo_3067_, 2);
                v___x_3079_ = lean_array_get_size(v_args_3072_);
                v___x_3080_ = lean_nat_dec_lt(v_recArgPos_3078_, v___x_3079_);
                if v___x_3080_ == 0 {
                    v___x_3081_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__1);
                    v___x_3082_ = l_Lean_indentExpr(v_e_3071_);
                    v___x_3083_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3083_, 0, v___x_3081_);
                    lean_ctor_set(v___x_3083_, 1, v___x_3082_);
                    v___x_3084_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v___x_3083_, v_a_3073_, v_a_3074_, v_a_3075_, v_a_3076_);
                    return v___x_3084_;
                } else {
                    v___x_3085_ = lean_array_fget_borrowed(v_args_3072_, v_recArgPos_3078_);
                    lean_inc(v___x_3085_);
                    v___x_3086_ = l_Lean_Meta_whnfCore(
                        v___x_3085_,
                        v_a_3073_,
                        v_a_3074_,
                        v_a_3075_,
                        v_a_3076_,
                    );
                    if lean_obj_tag(v___x_3086_) == 0 {
                        v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
                        lean_inc(v_a_3087_);
                        lean_dec_ref_known(v___x_3086_, 1);
                        v___x_3097_ = l_Lean_Expr_getAppFn(v_a_3087_);
                        if lean_obj_tag(v___x_3097_) == 1 {
                            v_fvarId_3098_ = lean_ctor_get(v___x_3097_, 0);
                            lean_inc(v_fvarId_3098_);
                            lean_dec_ref_known(v___x_3097_, 1);
                            v_motives_3099_ = lean_ctor_get(v_ctx_3068_, 1);
                            v___x_3100_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(v_motives_3099_, v_fvarId_3098_);
                            lean_dec(v_fvarId_3098_);
                            if lean_obj_tag(v___x_3100_) == 1 {
                                v_val_3101_ = lean_ctor_get(v___x_3100_, 0);
                                lean_inc(v_val_3101_);
                                lean_dec_ref_known(v___x_3100_, 1);
                                v_fst_3102_ = lean_ctor_get(v_val_3101_, 0);
                                lean_inc(v_fst_3102_);
                                v_snd_3103_ = lean_ctor_get(v_val_3101_, 1);
                                lean_inc(v_snd_3103_);
                                lean_dec(v_val_3101_);
                                v___x_3104_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__4);
                                v___x_3105_ = lean_array_get_borrowed(
                                    v___x_3104_,
                                    v_positions_3070_,
                                    v_fst_3102_,
                                );
                                lean_dec(v_fst_3102_);
                                v___x_3106_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__2(v___x_3105_, v_fidx_3069_);
                                if lean_obj_tag(v___x_3106_) == 1 {
                                    lean_dec_ref(v_e_3071_);
                                    v_val_3107_ = lean_ctor_get(v___x_3106_, 0);
                                    lean_inc(v_val_3107_);
                                    lean_dec_ref_known(v___x_3106_, 1);
                                    v___x_3108_ = lean_unsigned_to_nat(0);
                                    v___x_3109_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5;
                                    v___x_3110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(v_recArgInfo_3067_, v_args_3072_, v___x_3079_, v_recArgPos_3078_, v___x_3108_, v___x_3109_);
                                    if lean_obj_tag(v___x_3110_) == 0 {
                                        v_a_3111_ = lean_ctor_get(v___x_3110_, 0);
                                        v_isSharedCheck_3128_ =
                                            (!lean_is_exclusive(v___x_3110_)) as u8;
                                        if v_isSharedCheck_3128_ == 0 {
                                            v___x_3113_ = v___x_3110_;
                                            v_isShared_3114_ = v_isSharedCheck_3128_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3111_);
                                            lean_dec(v___x_3110_);
                                            v___x_3113_ = lean_box(0);
                                            v_isShared_3114_ = v_isSharedCheck_3128_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_val_3107_);
                                        lean_dec(v_snd_3103_);
                                        lean_dec(v_a_3087_);
                                        v_a_3129_ = lean_ctor_get(v___x_3110_, 0);
                                        v_isSharedCheck_3136_ =
                                            (!lean_is_exclusive(v___x_3110_)) as u8;
                                        if v_isSharedCheck_3136_ == 0 {
                                            v___x_3131_ = v___x_3110_;
                                            v_isShared_3132_ = v_isSharedCheck_3136_;
                                            state = 4;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3129_);
                                            lean_dec(v___x_3110_);
                                            v___x_3131_ = lean_box(0);
                                            v_isShared_3132_ = v_isSharedCheck_3136_;
                                            state = 4;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v___x_3106_);
                                    lean_dec(v_snd_3103_);
                                    lean_dec(v_a_3087_);
                                    v___y_3089_ = v_a_3073_;
                                    v___y_3090_ = v_a_3074_;
                                    v___y_3091_ = v_a_3075_;
                                    v___y_3092_ = v_a_3076_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_3100_);
                                lean_dec(v_a_3087_);
                                v___y_3089_ = v_a_3073_;
                                v___y_3090_ = v_a_3074_;
                                v___y_3091_ = v_a_3075_;
                                v___y_3092_ = v_a_3076_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v___x_3097_);
                            lean_dec(v_a_3087_);
                            v___y_3089_ = v_a_3073_;
                            v___y_3090_ = v_a_3074_;
                            v___y_3091_ = v_a_3075_;
                            v___y_3092_ = v_a_3076_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_3071_);
                        return v___x_3086_;
                    }
                }
            }
            1 => {
                v___x_3093_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__3);
                v___x_3094_ = l_Lean_indentExpr(v_e_3071_);
                v___x_3095_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3095_, 0, v___x_3093_);
                lean_ctor_set(v___x_3095_, 1, v___x_3094_);
                v___x_3096_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v___x_3095_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
                return v___x_3096_;
            }
            2 => {
                v_nargs_3115_ = l_Lean_Expr_getAppNumArgs(v_a_3087_);
                v_dummy_3116_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                lean_inc(v_nargs_3115_);
                v___x_3117_ = lean_mk_array(v_nargs_3115_, v_dummy_3116_);
                v___x_3118_ = lean_unsigned_to_nat(1);
                v___x_3119_ = lean_nat_sub(v_nargs_3115_, v___x_3118_);
                lean_dec(v_nargs_3115_);
                v___x_3120_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_a_3087_,
                    v___x_3117_,
                    v___x_3119_,
                );
                v___x_3121_ = l_Lean_mkAppN(v_snd_3103_, v___x_3120_);
                lean_dec_ref(v___x_3120_);
                v___x_3122_ = lean_array_get_size(v___x_3105_);
                v___x_3123_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_andProj(v_val_3107_, v___x_3122_, v___x_3121_);
                v___x_3124_ = l_Lean_mkAppN(v___x_3123_, v_a_3111_);
                lean_dec(v_a_3111_);
                if v_isShared_3114_ == 0 {
                    lean_ctor_set(v___x_3113_, 0, v___x_3124_);
                    v___x_3126_ = v___x_3113_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
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
                    v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
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
    mut v_recArgInfo_3137_: *mut LeanObject,
    mut v_ctx_3138_: *mut LeanObject,
    mut v_fidx_3139_: *mut LeanObject,
    mut v_positions_3140_: *mut LeanObject,
    mut v_e_3141_: *mut LeanObject,
    mut v_args_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
    mut v_a_3144_: *mut LeanObject,
    mut v_a_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3148_: *mut LeanObject = core::ptr::null_mut();
    v_res_3148_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp(v_recArgInfo_3137_, v_ctx_3138_, v_fidx_3139_, v_positions_3140_, v_e_3141_, v_args_3142_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
    lean_dec(v_a_3146_);
    lean_dec_ref(v_a_3145_);
    lean_dec(v_a_3144_);
    lean_dec_ref(v_a_3143_);
    lean_dec_ref(v_args_3142_);
    lean_dec_ref(v_positions_3140_);
    lean_dec(v_fidx_3139_);
    lean_dec_ref(v_ctx_3138_);
    lean_dec_ref(v_recArgInfo_3137_);
    return v_res_3148_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0(
    mut v_00_u03b1_3149_: *mut LeanObject,
    mut v_msg_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
    mut v___y_3152_: *mut LeanObject,
    mut v___y_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    v___x_3156_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___redArg(v_msg_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
    return v___x_3156_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0___boxed(
    mut v_00_u03b1_3157_: *mut LeanObject,
    mut v_msg_3158_: *mut LeanObject,
    mut v___y_3159_: *mut LeanObject,
    mut v___y_3160_: *mut LeanObject,
    mut v___y_3161_: *mut LeanObject,
    mut v___y_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3164_: *mut LeanObject = core::ptr::null_mut();
    v_res_3164_ = l_Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0(v_00_u03b1_3157_, v_msg_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
    lean_dec(v___y_3162_);
    lean_dec_ref(v___y_3161_);
    lean_dec(v___y_3160_);
    lean_dec_ref(v___y_3159_);
    return v_res_3164_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1(
    mut v_00_u03b4_3165_: *mut LeanObject,
    mut v_t_3166_: *mut LeanObject,
    mut v_k_3167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    v___x_3168_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___redArg(v_t_3166_, v_k_3167_);
    return v___x_3168_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1___boxed(
    mut v_00_u03b4_3169_: *mut LeanObject,
    mut v_t_3170_: *mut LeanObject,
    mut v_k_3171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3172_: *mut LeanObject = core::ptr::null_mut();
    v_res_3172_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__1(v_00_u03b4_3169_, v_t_3170_, v_k_3171_);
    lean_dec(v_k_3171_);
    lean_dec(v_t_3170_);
    return v_res_3172_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4(
    mut v_recArgInfo_3173_: *mut LeanObject,
    mut v_args_3174_: *mut LeanObject,
    mut v_upperBound_3175_: *mut LeanObject,
    mut v___x_3176_: *mut LeanObject,
    mut v_inst_3177_: *mut LeanObject,
    mut v_R_3178_: *mut LeanObject,
    mut v_a_3179_: *mut LeanObject,
    mut v_b_3180_: *mut LeanObject,
    mut v_c_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
    mut v___y_3183_: *mut LeanObject,
    mut v___y_3184_: *mut LeanObject,
    mut v___y_3185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    v___x_3187_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___redArg(v_recArgInfo_3173_, v_args_3174_, v_upperBound_3175_, v___x_3176_, v_a_3179_, v_b_3180_);
    return v___x_3187_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4___boxed(
    mut v_recArgInfo_3188_: *mut LeanObject,
    mut v_args_3189_: *mut LeanObject,
    mut v_upperBound_3190_: *mut LeanObject,
    mut v___x_3191_: *mut LeanObject,
    mut v_inst_3192_: *mut LeanObject,
    mut v_R_3193_: *mut LeanObject,
    mut v_a_3194_: *mut LeanObject,
    mut v_b_3195_: *mut LeanObject,
    mut v_c_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
    mut v___y_3198_: *mut LeanObject,
    mut v___y_3199_: *mut LeanObject,
    mut v___y_3200_: *mut LeanObject,
    mut v___y_3201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3202_: *mut LeanObject = core::ptr::null_mut();
    v_res_3202_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__4(v_recArgInfo_3188_, v_args_3189_, v_upperBound_3190_, v___x_3191_, v_inst_3192_, v_R_3193_, v_a_3194_, v_b_3195_, v_c_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
    lean_dec(v___y_3200_);
    lean_dec_ref(v___y_3199_);
    lean_dec(v___y_3198_);
    lean_dec_ref(v___y_3197_);
    lean_dec(v___x_3191_);
    lean_dec(v_upperBound_3190_);
    lean_dec_ref(v_args_3189_);
    lean_dec_ref(v_recArgInfo_3188_);
    return v_res_3202_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0(
    mut v_k_3203_: *mut LeanObject,
    mut v___y_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
    mut v_b_3206_: *mut LeanObject,
    mut v___y_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
    mut v___y_3209_: *mut LeanObject,
    mut v___y_3210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3210_);
    lean_inc_ref(v___y_3209_);
    lean_inc(v___y_3208_);
    lean_inc_ref(v___y_3207_);
    lean_inc(v___y_3205_);
    lean_inc(v___y_3204_);
    v___x_3212_ = lean_apply_8(
        v_k_3203_,
        v_b_3206_,
        v___y_3204_,
        v___y_3205_,
        v___y_3207_,
        v___y_3208_,
        v___y_3209_,
        v___y_3210_,
        lean_box(0),
    );
    return v___x_3212_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0___boxed(
    mut v_k_3213_: *mut LeanObject,
    mut v___y_3214_: *mut LeanObject,
    mut v___y_3215_: *mut LeanObject,
    mut v_b_3216_: *mut LeanObject,
    mut v___y_3217_: *mut LeanObject,
    mut v___y_3218_: *mut LeanObject,
    mut v___y_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3222_: *mut LeanObject = core::ptr::null_mut();
    v_res_3222_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0(v_k_3213_, v___y_3214_, v___y_3215_, v_b_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
    lean_dec(v___y_3220_);
    lean_dec_ref(v___y_3219_);
    lean_dec(v___y_3218_);
    lean_dec_ref(v___y_3217_);
    lean_dec(v___y_3215_);
    lean_dec(v___y_3214_);
    return v_res_3222_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(
    mut v_name_3223_: *mut LeanObject,
    mut v_bi_3224_: u8,
    mut v_type_3225_: *mut LeanObject,
    mut v_k_3226_: *mut LeanObject,
    mut v_kind_3227_: u8,
    mut v___y_3228_: *mut LeanObject,
    mut v___y_3229_: *mut LeanObject,
    mut v___y_3230_: *mut LeanObject,
    mut v___y_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3229_);
                lean_inc(v___y_3228_);
                v___f_3235_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                lean_closure_set(v___f_3235_, 0, v_k_3226_);
                lean_closure_set(v___f_3235_, 1, v___y_3228_);
                lean_closure_set(v___f_3235_, 2, v___y_3229_);
                v___x_3236_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_3236_) == 0 {
                    return v___x_3236_;
                } else {
                    v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
                    v_isSharedCheck_3244_ = (!lean_is_exclusive(v___x_3236_)) as u8;
                    if v_isSharedCheck_3244_ == 0 {
                        v___x_3239_ = v___x_3236_;
                        v_isShared_3240_ = v_isSharedCheck_3244_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3237_);
                        lean_dec(v___x_3236_);
                        v___x_3239_ = lean_box(0);
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
                    v_reuseFailAlloc_3243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_a_3237_);
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
    mut v_name_3245_: *mut LeanObject,
    mut v_bi_3246_: *mut LeanObject,
    mut v_type_3247_: *mut LeanObject,
    mut v_k_3248_: *mut LeanObject,
    mut v_kind_3249_: *mut LeanObject,
    mut v___y_3250_: *mut LeanObject,
    mut v___y_3251_: *mut LeanObject,
    mut v___y_3252_: *mut LeanObject,
    mut v___y_3253_: *mut LeanObject,
    mut v___y_3254_: *mut LeanObject,
    mut v___y_3255_: *mut LeanObject,
    mut v___y_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3257_: u8 = 0;
    let mut v_kind_boxed_3258_: u8 = 0;
    let mut v_res_3259_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3257_ = (lean_unbox(v_bi_3246_) as u8);
    v_kind_boxed_3258_ = (lean_unbox(v_kind_3249_) as u8);
    v_res_3259_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_name_3245_, v_bi_boxed_3257_, v_type_3247_, v_k_3248_, v_kind_boxed_3258_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
    lean_dec(v___y_3255_);
    lean_dec_ref(v___y_3254_);
    lean_dec(v___y_3253_);
    lean_dec_ref(v___y_3252_);
    lean_dec(v___y_3251_);
    lean_dec(v___y_3250_);
    return v_res_3259_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3(
    mut v_00_u03b1_3260_: *mut LeanObject,
    mut v_name_3261_: *mut LeanObject,
    mut v_bi_3262_: u8,
    mut v_type_3263_: *mut LeanObject,
    mut v_k_3264_: *mut LeanObject,
    mut v_kind_3265_: u8,
    mut v___y_3266_: *mut LeanObject,
    mut v___y_3267_: *mut LeanObject,
    mut v___y_3268_: *mut LeanObject,
    mut v___y_3269_: *mut LeanObject,
    mut v___y_3270_: *mut LeanObject,
    mut v___y_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    v___x_3273_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_name_3261_, v_bi_3262_, v_type_3263_, v_k_3264_, v_kind_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
    return v___x_3273_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___boxed(
    mut v_00_u03b1_3274_: *mut LeanObject,
    mut v_name_3275_: *mut LeanObject,
    mut v_bi_3276_: *mut LeanObject,
    mut v_type_3277_: *mut LeanObject,
    mut v_k_3278_: *mut LeanObject,
    mut v_kind_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
    mut v___y_3282_: *mut LeanObject,
    mut v___y_3283_: *mut LeanObject,
    mut v___y_3284_: *mut LeanObject,
    mut v___y_3285_: *mut LeanObject,
    mut v___y_3286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3287_: u8 = 0;
    let mut v_kind_boxed_3288_: u8 = 0;
    let mut v_res_3289_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3287_ = (lean_unbox(v_bi_3276_) as u8);
    v_kind_boxed_3288_ = (lean_unbox(v_kind_3279_) as u8);
    v_res_3289_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3(v_00_u03b1_3274_, v_name_3275_, v_bi_boxed_3287_, v_type_3277_, v_k_3278_, v_kind_boxed_3288_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
    lean_dec(v___y_3285_);
    lean_dec_ref(v___y_3284_);
    lean_dec(v___y_3283_);
    lean_dec_ref(v___y_3282_);
    lean_dec(v___y_3281_);
    lean_dec(v___y_3280_);
    return v_res_3289_;
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0(
    mut v_k_3290_: *mut LeanObject,
    mut v_usedLetOnly_3291_: u8,
    mut v_x_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
    mut v___y_3294_: *mut LeanObject,
    mut v___y_3295_: *mut LeanObject,
    mut v___y_3296_: *mut LeanObject,
    mut v___y_3297_: *mut LeanObject,
    mut v___y_3298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3298_);
    lean_inc_ref(v___y_3297_);
    lean_inc(v___y_3296_);
    lean_inc_ref(v___y_3295_);
    lean_inc(v___y_3294_);
    lean_inc(v___y_3293_);
    lean_inc_ref(v_x_3292_);
    v___x_3300_ = lean_apply_8(
        v_k_3290_,
        v_x_3292_,
        v___y_3293_,
        v___y_3294_,
        v___y_3295_,
        v___y_3296_,
        v___y_3297_,
        v___y_3298_,
        lean_box(0),
    );
    if lean_obj_tag(v___x_3300_) == 0 {
        let mut v_a_3301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3305_: u8 = 0;
        let mut v___x_3306_: u8 = 0;
        let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
        v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
        lean_inc(v_a_3301_);
        lean_dec_ref_known(v___x_3300_, 1);
        v___x_3302_ = lean_unsigned_to_nat(1);
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
        lean_dec_ref(v___x_3304_);
        return v___x_3307_;
    } else {
        lean_dec_ref(v_x_3292_);
        return v___x_3300_;
    }
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0___boxed(
    mut v_k_3308_: *mut LeanObject,
    mut v_usedLetOnly_3309_: *mut LeanObject,
    mut v_x_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
    mut v___y_3312_: *mut LeanObject,
    mut v___y_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
    mut v___y_3315_: *mut LeanObject,
    mut v___y_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_usedLetOnly_boxed_3318_: u8 = 0;
    let mut v_res_3319_: *mut LeanObject = core::ptr::null_mut();
    v_usedLetOnly_boxed_3318_ = (lean_unbox(v_usedLetOnly_3309_) as u8);
    v_res_3319_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0(v_k_3308_, v_usedLetOnly_boxed_3318_, v_x_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_);
    lean_dec(v___y_3316_);
    lean_dec_ref(v___y_3315_);
    lean_dec(v___y_3314_);
    lean_dec_ref(v___y_3313_);
    lean_dec(v___y_3312_);
    lean_dec(v___y_3311_);
    return v_res_3319_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(
    mut v_name_3320_: *mut LeanObject,
    mut v_type_3321_: *mut LeanObject,
    mut v_val_3322_: *mut LeanObject,
    mut v_k_3323_: *mut LeanObject,
    mut v_nondep_3324_: u8,
    mut v_kind_3325_: u8,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3338_: u8 = 0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3327_);
                lean_inc(v___y_3326_);
                v___f_3333_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 9, 3);
                lean_closure_set(v___f_3333_, 0, v_k_3323_);
                lean_closure_set(v___f_3333_, 1, v___y_3326_);
                lean_closure_set(v___f_3333_, 2, v___y_3327_);
                v___x_3334_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_3334_) == 0 {
                    return v___x_3334_;
                } else {
                    v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
                    v_isSharedCheck_3342_ = (!lean_is_exclusive(v___x_3334_)) as u8;
                    if v_isSharedCheck_3342_ == 0 {
                        v___x_3337_ = v___x_3334_;
                        v_isShared_3338_ = v_isSharedCheck_3342_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3335_);
                        lean_dec(v___x_3334_);
                        v___x_3337_ = lean_box(0);
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
                    v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
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
    mut v_name_3343_: *mut LeanObject,
    mut v_type_3344_: *mut LeanObject,
    mut v_val_3345_: *mut LeanObject,
    mut v_k_3346_: *mut LeanObject,
    mut v_nondep_3347_: *mut LeanObject,
    mut v_kind_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
    mut v___y_3353_: *mut LeanObject,
    mut v___y_3354_: *mut LeanObject,
    mut v___y_3355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_3356_: u8 = 0;
    let mut v_kind_boxed_3357_: u8 = 0;
    let mut v_res_3358_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3356_ = (lean_unbox(v_nondep_3347_) as u8);
    v_kind_boxed_3357_ = (lean_unbox(v_kind_3348_) as u8);
    v_res_3358_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(v_name_3343_, v_type_3344_, v_val_3345_, v_k_3346_, v_nondep_boxed_3356_, v_kind_boxed_3357_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_, v___y_3353_, v___y_3354_);
    lean_dec(v___y_3354_);
    lean_dec_ref(v___y_3353_);
    lean_dec(v___y_3352_);
    lean_dec_ref(v___y_3351_);
    lean_dec(v___y_3350_);
    lean_dec(v___y_3349_);
    return v_res_3358_;
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4(
    mut v_name_3359_: *mut LeanObject,
    mut v_type_3360_: *mut LeanObject,
    mut v_val_3361_: *mut LeanObject,
    mut v_k_3362_: *mut LeanObject,
    mut v_nondep_3363_: u8,
    mut v_kind_3364_: u8,
    mut v_usedLetOnly_3365_: u8,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    v___x_3373_ = lean_box((v_usedLetOnly_3365_) as usize);
    v___f_3374_ = lean_alloc_closure(l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___lam__0___boxed as *mut core::ffi::c_void, 10, 2);
    lean_closure_set(v___f_3374_, 0, v_k_3362_);
    lean_closure_set(v___f_3374_, 1, v___x_3373_);
    v___x_3375_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(v_name_3359_, v_type_3360_, v_val_3361_, v___f_3374_, v_nondep_3363_, v_kind_3364_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    return v___x_3375_;
}
pub unsafe fn l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4___boxed(
    mut v_name_3376_: *mut LeanObject,
    mut v_type_3377_: *mut LeanObject,
    mut v_val_3378_: *mut LeanObject,
    mut v_k_3379_: *mut LeanObject,
    mut v_nondep_3380_: *mut LeanObject,
    mut v_kind_3381_: *mut LeanObject,
    mut v_usedLetOnly_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
    mut v___y_3388_: *mut LeanObject,
    mut v___y_3389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_3390_: u8 = 0;
    let mut v_kind_boxed_3391_: u8 = 0;
    let mut v_usedLetOnly_boxed_3392_: u8 = 0;
    let mut v_res_3393_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3390_ = (lean_unbox(v_nondep_3380_) as u8);
    v_kind_boxed_3391_ = (lean_unbox(v_kind_3381_) as u8);
    v_usedLetOnly_boxed_3392_ = (lean_unbox(v_usedLetOnly_3382_) as u8);
    v_res_3393_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4(v_name_3376_, v_type_3377_, v_val_3378_, v_k_3379_, v_nondep_boxed_3390_, v_kind_boxed_3391_, v_usedLetOnly_boxed_3392_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
    lean_dec(v___y_3388_);
    lean_dec_ref(v___y_3387_);
    lean_dec(v___y_3386_);
    lean_dec_ref(v___y_3385_);
    lean_dec(v___y_3384_);
    lean_dec(v___y_3383_);
    return v_res_3393_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3(
    mut v_xs_3394_: *mut LeanObject,
    mut v_v_3395_: *mut LeanObject,
    mut v_i_3396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3397_ = lean_array_get_size(v_xs_3394_);
                v___x_3398_ = lean_nat_dec_lt(v_i_3396_, v___x_3397_);
                if v___x_3398_ == 0 {
                    lean_dec(v_i_3396_);
                    v___x_3399_ = lean_box(0);
                    return v___x_3399_;
                } else {
                    v___x_3400_ = lean_array_fget_borrowed(v_xs_3394_, v_i_3396_);
                    v___x_3401_ = lean_name_eq(v___x_3400_, v_v_3395_);
                    if v___x_3401_ == 0 {
                        v___x_3402_ = lean_unsigned_to_nat(1);
                        v___x_3403_ = lean_nat_add(v_i_3396_, v___x_3402_);
                        lean_dec(v_i_3396_);
                        v_i_3396_ = v___x_3403_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3405_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3405_, 0, v_i_3396_);
                        return v___x_3405_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3___boxed(
    mut v_xs_3406_: *mut LeanObject,
    mut v_v_3407_: *mut LeanObject,
    mut v_i_3408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3409_: *mut LeanObject = core::ptr::null_mut();
    v_res_3409_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3(v_xs_3406_, v_v_3407_, v_i_3408_);
    lean_dec(v_v_3407_);
    lean_dec_ref(v_xs_3406_);
    return v_res_3409_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1(
    mut v_xs_3410_: *mut LeanObject,
    mut v_v_3411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    v___x_3412_ = lean_unsigned_to_nat(0);
    v___x_3413_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1_spec__3(v_xs_3410_, v_v_3411_, v___x_3412_);
    return v___x_3413_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1___boxed(
    mut v_xs_3414_: *mut LeanObject,
    mut v_v_3415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3416_: *mut LeanObject = core::ptr::null_mut();
    v_res_3416_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1(v_xs_3414_, v_v_3415_);
    lean_dec(v_v_3415_);
    lean_dec_ref(v_xs_3414_);
    return v_res_3416_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1(
    mut v_xs_3417_: *mut LeanObject,
    mut v_v_3418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3424_: u8 = 0;
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3428_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3419_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1_spec__1(v_xs_3417_, v_v_3418_);
                if lean_obj_tag(v___x_3419_) == 0 {
                    v___x_3420_ = lean_box(0);
                    return v___x_3420_;
                } else {
                    v_val_3421_ = lean_ctor_get(v___x_3419_, 0);
                    v_isSharedCheck_3428_ = (!lean_is_exclusive(v___x_3419_)) as u8;
                    if v_isSharedCheck_3428_ == 0 {
                        v___x_3423_ = v___x_3419_;
                        v_isShared_3424_ = v_isSharedCheck_3428_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3421_);
                        lean_dec(v___x_3419_);
                        v___x_3423_ = lean_box(0);
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
                    v_reuseFailAlloc_3427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3427_, 0, v_val_3421_);
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
    mut v_xs_3429_: *mut LeanObject,
    mut v_v_3430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3431_: *mut LeanObject = core::ptr::null_mut();
    v_res_3431_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1(v_xs_3429_, v_v_3430_);
    lean_dec(v_v_3430_);
    lean_dec_ref(v_xs_3429_);
    return v_res_3431_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0()
-> f64 {
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: f64 = 0.0;
    v___x_3432_ = lean_unsigned_to_nat(0);
    v___x_3433_ = lean_float_of_nat(v___x_3432_);
    return v___x_3433_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(
    mut v_cls_3437_: *mut LeanObject,
    mut v_msg_3438_: *mut LeanObject,
    mut v___y_3439_: *mut LeanObject,
    mut v___y_3440_: *mut LeanObject,
    mut v___y_3441_: *mut LeanObject,
    mut v___y_3442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v_tid_3463_: u64 = 0;
    let mut v_traces_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: f64 = 0.0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3488_: u8 = 0;
    let mut v_isSharedCheck_3489_: u8 = 0;
    let mut v_isSharedCheck_3490_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3444_ = lean_ctor_get(v___y_3441_, 5);
                v___x_3445_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msg_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
                v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
                v_isSharedCheck_3490_ = (!lean_is_exclusive(v___x_3445_)) as u8;
                if v_isSharedCheck_3490_ == 0 {
                    v___x_3448_ = v___x_3445_;
                    v_isShared_3449_ = v_isSharedCheck_3490_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3446_);
                    lean_dec(v___x_3445_);
                    v___x_3448_ = lean_box(0);
                    v_isShared_3449_ = v_isSharedCheck_3490_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3450_ = lean_st_ref_take(v___y_3442_);
                v_traceState_3451_ = lean_ctor_get(v___x_3450_, 4);
                v_env_3452_ = lean_ctor_get(v___x_3450_, 0);
                v_nextMacroScope_3453_ = lean_ctor_get(v___x_3450_, 1);
                v_ngen_3454_ = lean_ctor_get(v___x_3450_, 2);
                v_auxDeclNGen_3455_ = lean_ctor_get(v___x_3450_, 3);
                v_cache_3456_ = lean_ctor_get(v___x_3450_, 5);
                v_messages_3457_ = lean_ctor_get(v___x_3450_, 6);
                v_infoState_3458_ = lean_ctor_get(v___x_3450_, 7);
                v_snapshotTasks_3459_ = lean_ctor_get(v___x_3450_, 8);
                v_isSharedCheck_3489_ = (!lean_is_exclusive(v___x_3450_)) as u8;
                if v_isSharedCheck_3489_ == 0 {
                    v___x_3461_ = v___x_3450_;
                    v_isShared_3462_ = v_isSharedCheck_3489_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3459_);
                    lean_inc(v_infoState_3458_);
                    lean_inc(v_messages_3457_);
                    lean_inc(v_cache_3456_);
                    lean_inc(v_traceState_3451_);
                    lean_inc(v_auxDeclNGen_3455_);
                    lean_inc(v_ngen_3454_);
                    lean_inc(v_nextMacroScope_3453_);
                    lean_inc(v_env_3452_);
                    lean_dec(v___x_3450_);
                    v___x_3461_ = lean_box(0);
                    v_isShared_3462_ = v_isSharedCheck_3489_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3463_ = lean_ctor_get_uint64(
                    v_traceState_3451_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_3464_ = lean_ctor_get(v_traceState_3451_, 0);
                v_isSharedCheck_3488_ = (!lean_is_exclusive(v_traceState_3451_)) as u8;
                if v_isSharedCheck_3488_ == 0 {
                    v___x_3466_ = v_traceState_3451_;
                    v_isShared_3467_ = v_isSharedCheck_3488_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_3464_);
                    lean_dec(v_traceState_3451_);
                    v___x_3466_ = lean_box(0);
                    v_isShared_3467_ = v_isSharedCheck_3488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3468_ = lean_box(0);
                v___x_3469_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__0);
                v___x_3470_ = 0;
                v___x_3471_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__1;
                v___x_3472_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_3472_, 0, v_cls_3437_);
                lean_ctor_set(v___x_3472_, 1, v___x_3468_);
                lean_ctor_set(v___x_3472_, 2, v___x_3471_);
                lean_ctor_set_float(
                    v___x_3472_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3469_,
                );
                lean_ctor_set_float(
                    v___x_3472_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_3469_,
                );
                lean_ctor_set_uint8(
                    v___x_3472_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_3470_,
                );
                v___x_3473_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg___closed__2;
                v___x_3474_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_3474_, 0, v___x_3472_);
                lean_ctor_set(v___x_3474_, 1, v_a_3446_);
                lean_ctor_set(v___x_3474_, 2, v___x_3473_);
                lean_inc(v_ref_3444_);
                v___x_3475_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3475_, 0, v_ref_3444_);
                lean_ctor_set(v___x_3475_, 1, v___x_3474_);
                v___x_3476_ = l_Lean_PersistentArray_push___redArg(v_traces_3464_, v___x_3475_);
                if v_isShared_3467_ == 0 {
                    lean_ctor_set(v___x_3466_, 0, v___x_3476_);
                    v___x_3478_ = v___x_3466_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3487_, 0, v___x_3476_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_3487_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_3463_,
                    );
                    v___x_3478_ = v_reuseFailAlloc_3487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3462_ == 0 {
                    lean_ctor_set(v___x_3461_, 4, v___x_3478_);
                    v___x_3480_ = v___x_3461_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_env_3452_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_nextMacroScope_3453_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_ngen_3454_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_auxDeclNGen_3455_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 4, v___x_3478_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 5, v_cache_3456_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 6, v_messages_3457_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 7, v_infoState_3458_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 8, v_snapshotTasks_3459_);
                    v___x_3480_ = v_reuseFailAlloc_3486_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3481_ = lean_st_ref_set(v___y_3442_, v___x_3480_);
                v___x_3482_ = lean_box(0);
                if v_isShared_3449_ == 0 {
                    lean_ctor_set(v___x_3448_, 0, v___x_3482_);
                    v___x_3484_ = v___x_3448_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
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
    mut v_cls_3491_: *mut LeanObject,
    mut v_msg_3492_: *mut LeanObject,
    mut v___y_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3498_: *mut LeanObject = core::ptr::null_mut();
    v_res_3498_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(v_cls_3491_, v_msg_3492_, v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_);
    lean_dec(v___y_3496_);
    lean_dec_ref(v___y_3495_);
    lean_dec(v___y_3494_);
    lean_dec_ref(v___y_3493_);
    return v_res_3498_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__6(
    mut v_e_3499_: *mut LeanObject,
    mut v_as_3500_: *mut LeanObject,
    mut v_i_3501_: usize,
    mut v_stop_3502_: usize,
) -> u8 {
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnName_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_3506_: *mut LeanObject = core::ptr::null_mut();
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
                    v_fnName_3505_ = lean_ctor_get(v___x_3504_, 0);
                    v_recArgPos_3506_ = lean_ctor_get(v___x_3504_, 2);
                    lean_inc(v_recArgPos_3506_);
                    lean_inc(v_fnName_3505_);
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
    mut v_e_3512_: *mut LeanObject,
    mut v_as_3513_: *mut LeanObject,
    mut v_i_3514_: *mut LeanObject,
    mut v_stop_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3516_: usize = 0;
    let mut v_stop_boxed_3517_: usize = 0;
    let mut v_res_3518_: u8 = 0;
    let mut v_r_3519_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3516_ = lean_unbox_usize(v_i_3514_);
    lean_dec(v_i_3514_);
    v_stop_boxed_3517_ = lean_unbox_usize(v_stop_3515_);
    lean_dec(v_stop_3515_);
    v_res_3518_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__6(v_e_3512_, v_as_3513_, v_i_boxed_3516_, v_stop_boxed_3517_);
    lean_dec_ref(v_as_3513_);
    lean_dec_ref(v_e_3512_);
    v_r_3519_ = lean_box((v_res_3518_) as usize);
    return v_r_3519_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    v___x_3520_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3520_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut LeanObject = core::ptr::null_mut();
    v___x_3521_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__0);
    v___x_3522_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3522_, 0, v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    v___x_3523_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_3524_ = lean_unsigned_to_nat(0);
    v___x_3525_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3525_, 0, v___x_3524_);
    lean_ctor_set(v___x_3525_, 1, v___x_3524_);
    lean_ctor_set(v___x_3525_, 2, v___x_3524_);
    lean_ctor_set(v___x_3525_, 3, v___x_3524_);
    lean_ctor_set(v___x_3525_, 4, v___x_3523_);
    lean_ctor_set(v___x_3525_, 5, v___x_3523_);
    lean_ctor_set(v___x_3525_, 6, v___x_3523_);
    lean_ctor_set(v___x_3525_, 7, v___x_3523_);
    lean_ctor_set(v___x_3525_, 8, v___x_3523_);
    lean_ctor_set(v___x_3525_, 9, v___x_3523_);
    return v___x_3525_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    v___x_3526_ = lean_unsigned_to_nat(32);
    v___x_3527_ = lean_mk_empty_array_with_capacity(v___x_3526_);
    v___x_3528_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3528_, 0, v___x_3527_);
    return v___x_3528_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3529_: usize = 0;
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    v___x_3529_ = 5usize;
    v___x_3530_ = lean_unsigned_to_nat(0);
    v___x_3531_ = lean_unsigned_to_nat(32);
    v___x_3532_ = lean_mk_empty_array_with_capacity(v___x_3531_);
    v___x_3533_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__3);
    v___x_3534_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3534_, 0, v___x_3533_);
    lean_ctor_set(v___x_3534_, 1, v___x_3532_);
    lean_ctor_set(v___x_3534_, 2, v___x_3530_);
    lean_ctor_set(v___x_3534_, 3, v___x_3530_);
    lean_ctor_set_usize(v___x_3534_, 4, v___x_3529_);
    return v___x_3534_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
    v___x_3535_ = lean_box(1);
    v___x_3536_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__4);
    v___x_3537_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__1);
    v___x_3538_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3538_, 0, v___x_3537_);
    lean_ctor_set(v___x_3538_, 1, v___x_3536_);
    lean_ctor_set(v___x_3538_, 2, v___x_3535_);
    return v___x_3538_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    v___x_3540_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__6;
    v___x_3541_ = l_Lean_stringToMessageData(v___x_3540_);
    return v___x_3541_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    v___x_3543_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__8;
    v___x_3544_ = l_Lean_stringToMessageData(v___x_3543_);
    return v___x_3544_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    v___x_3546_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__10;
    v___x_3547_ = l_Lean_stringToMessageData(v___x_3546_);
    return v___x_3547_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    v___x_3549_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__12;
    v___x_3550_ = l_Lean_stringToMessageData(v___x_3549_);
    return v___x_3550_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    v___x_3552_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__14;
    v___x_3553_ = l_Lean_stringToMessageData(v___x_3552_);
    return v___x_3553_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    v___x_3555_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__16;
    v___x_3556_ = l_Lean_stringToMessageData(v___x_3555_);
    return v___x_3556_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__18;
    v___x_3559_ = l_Lean_stringToMessageData(v___x_3558_);
    return v___x_3559_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(
    mut v_msg_3560_: *mut LeanObject,
    mut v_declHint_3561_: *mut LeanObject,
    mut v___y_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: u8 = 0;
    let mut v_isExporting_3567_: u8 = 0;
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: u8 = 0;
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3589_: u8 = 0;
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3621_: u8 = 0;
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3564_ = lean_st_ref_get(v___y_3562_);
                v_env_3565_ = lean_ctor_get(v___x_3564_, 0);
                lean_inc_ref(v_env_3565_);
                lean_dec(v___x_3564_);
                v___x_3566_ = l_Lean_Name_isAnonymous(v_declHint_3561_);
                if v___x_3566_ == 0 {
                    v_isExporting_3567_ = lean_ctor_get_uint8(
                        v_env_3565_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3567_ == 0 {
                        lean_dec_ref(v_env_3565_);
                        lean_dec(v_declHint_3561_);
                        v___x_3568_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3568_, 0, v_msg_3560_);
                        return v___x_3568_;
                    } else {
                        lean_inc_ref(v_env_3565_);
                        v___x_3569_ = l_Lean_Environment_setExporting(v_env_3565_, v___x_3566_);
                        lean_inc(v_declHint_3561_);
                        lean_inc_ref(v___x_3569_);
                        v___x_3570_ = l_Lean_Environment_contains(
                            v___x_3569_,
                            v_declHint_3561_,
                            v_isExporting_3567_,
                        );
                        if v___x_3570_ == 0 {
                            lean_dec_ref(v___x_3569_);
                            lean_dec_ref(v_env_3565_);
                            lean_dec(v_declHint_3561_);
                            v___x_3571_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3571_, 0, v_msg_3560_);
                            return v___x_3571_;
                        } else {
                            v___x_3572_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__2);
                            v___x_3573_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__5);
                            v___x_3574_ = l_Lean_Options_empty;
                            v___x_3575_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3575_, 0, v___x_3569_);
                            lean_ctor_set(v___x_3575_, 1, v___x_3572_);
                            lean_ctor_set(v___x_3575_, 2, v___x_3573_);
                            lean_ctor_set(v___x_3575_, 3, v___x_3574_);
                            lean_inc(v_declHint_3561_);
                            v___x_3576_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3561_, v___x_3566_);
                            v_c_3577_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3577_, 0, v___x_3575_);
                            lean_ctor_set(v_c_3577_, 1, v___x_3576_);
                            v___x_3578_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3565_,
                                v_declHint_3561_,
                            );
                            if lean_obj_tag(v___x_3578_) == 0 {
                                lean_dec_ref(v_env_3565_);
                                lean_dec(v_declHint_3561_);
                                v___x_3579_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
                                v___x_3580_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3580_, 0, v___x_3579_);
                                lean_ctor_set(v___x_3580_, 1, v_c_3577_);
                                v___x_3581_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__9);
                                v___x_3582_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3582_, 0, v___x_3580_);
                                lean_ctor_set(v___x_3582_, 1, v___x_3581_);
                                v___x_3583_ = l_Lean_MessageData_note(v___x_3582_);
                                v___x_3584_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3584_, 0, v_msg_3560_);
                                lean_ctor_set(v___x_3584_, 1, v___x_3583_);
                                v___x_3585_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3585_, 0, v___x_3584_);
                                return v___x_3585_;
                            } else {
                                v_val_3586_ = lean_ctor_get(v___x_3578_, 0);
                                v_isSharedCheck_3621_ = (!lean_is_exclusive(v___x_3578_)) as u8;
                                if v_isSharedCheck_3621_ == 0 {
                                    v___x_3588_ = v___x_3578_;
                                    v_isShared_3589_ = v_isSharedCheck_3621_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3586_);
                                    lean_dec(v___x_3578_);
                                    v___x_3588_ = lean_box(0);
                                    v_isShared_3589_ = v_isSharedCheck_3621_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3565_);
                    lean_dec(v_declHint_3561_);
                    v___x_3622_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3622_, 0, v_msg_3560_);
                    return v___x_3622_;
                }
            }
            1 => {
                v___x_3590_ = lean_box(0);
                v___x_3591_ = l_Lean_Environment_header(v_env_3565_);
                lean_dec_ref(v_env_3565_);
                v___x_3592_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3591_);
                v_mod_3593_ = lean_array_get(v___x_3590_, v___x_3592_, v_val_3586_);
                lean_dec(v_val_3586_);
                lean_dec_ref(v___x_3592_);
                v___x_3594_ = l_Lean_isPrivateName(v_declHint_3561_);
                lean_dec(v_declHint_3561_);
                if v___x_3594_ == 0 {
                    v___x_3595_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__11);
                    v___x_3596_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3596_, 0, v___x_3595_);
                    lean_ctor_set(v___x_3596_, 1, v_c_3577_);
                    v___x_3597_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__13);
                    v___x_3598_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3598_, 0, v___x_3596_);
                    lean_ctor_set(v___x_3598_, 1, v___x_3597_);
                    v___x_3599_ = l_Lean_MessageData_ofName(v_mod_3593_);
                    v___x_3600_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3600_, 0, v___x_3598_);
                    lean_ctor_set(v___x_3600_, 1, v___x_3599_);
                    v___x_3601_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__15);
                    v___x_3602_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3602_, 0, v___x_3600_);
                    lean_ctor_set(v___x_3602_, 1, v___x_3601_);
                    v___x_3603_ = l_Lean_MessageData_note(v___x_3602_);
                    v___x_3604_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3604_, 0, v_msg_3560_);
                    lean_ctor_set(v___x_3604_, 1, v___x_3603_);
                    if v_isShared_3589_ == 0 {
                        lean_ctor_set_tag(v___x_3588_, 0);
                        lean_ctor_set(v___x_3588_, 0, v___x_3604_);
                        v___x_3606_ = v___x_3588_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
                        v___x_3606_ = v_reuseFailAlloc_3607_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3608_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__7);
                    v___x_3609_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3609_, 0, v___x_3608_);
                    lean_ctor_set(v___x_3609_, 1, v_c_3577_);
                    v___x_3610_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__17);
                    v___x_3611_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3611_, 0, v___x_3609_);
                    lean_ctor_set(v___x_3611_, 1, v___x_3610_);
                    v___x_3612_ = l_Lean_MessageData_ofName(v_mod_3593_);
                    v___x_3613_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3613_, 0, v___x_3611_);
                    lean_ctor_set(v___x_3613_, 1, v___x_3612_);
                    v___x_3614_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg___closed__19);
                    v___x_3615_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3615_, 0, v___x_3613_);
                    lean_ctor_set(v___x_3615_, 1, v___x_3614_);
                    v___x_3616_ = l_Lean_MessageData_note(v___x_3615_);
                    v___x_3617_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3617_, 0, v_msg_3560_);
                    lean_ctor_set(v___x_3617_, 1, v___x_3616_);
                    if v_isShared_3589_ == 0 {
                        lean_ctor_set_tag(v___x_3588_, 0);
                        lean_ctor_set(v___x_3588_, 0, v___x_3617_);
                        v___x_3619_ = v___x_3588_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3617_);
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
    mut v_msg_3623_: *mut LeanObject,
    mut v_declHint_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3627_: *mut LeanObject = core::ptr::null_mut();
    v_res_3627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3623_, v_declHint_3624_, v___y_3625_);
    lean_dec(v___y_3625_);
    return v_res_3627_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17(
    mut v_msg_3628_: *mut LeanObject,
    mut v_declHint_3629_: *mut LeanObject,
    mut v___y_3630_: *mut LeanObject,
    mut v___y_3631_: *mut LeanObject,
    mut v___y_3632_: *mut LeanObject,
    mut v___y_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3641_: u8 = 0;
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_3628_, v_declHint_3629_, v___y_3635_);
                v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
                v_isSharedCheck_3647_ = (!lean_is_exclusive(v___x_3637_)) as u8;
                if v_isSharedCheck_3647_ == 0 {
                    v___x_3640_ = v___x_3637_;
                    v_isShared_3641_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3638_);
                    lean_dec(v___x_3637_);
                    v___x_3640_ = lean_box(0);
                    v_isShared_3641_ = v_isSharedCheck_3647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3642_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3643_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3643_, 0, v___x_3642_);
                lean_ctor_set(v___x_3643_, 1, v_a_3638_);
                if v_isShared_3641_ == 0 {
                    lean_ctor_set(v___x_3640_, 0, v___x_3643_);
                    v___x_3645_ = v___x_3640_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3643_);
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
    mut v_msg_3648_: *mut LeanObject,
    mut v_declHint_3649_: *mut LeanObject,
    mut v___y_3650_: *mut LeanObject,
    mut v___y_3651_: *mut LeanObject,
    mut v___y_3652_: *mut LeanObject,
    mut v___y_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
    mut v___y_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3657_: *mut LeanObject = core::ptr::null_mut();
    v_res_3657_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17(v_msg_3648_, v_declHint_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_, v___y_3655_);
    lean_dec(v___y_3655_);
    lean_dec_ref(v___y_3654_);
    lean_dec(v___y_3653_);
    lean_dec_ref(v___y_3652_);
    lean_dec(v___y_3651_);
    lean_dec(v___y_3650_);
    return v_res_3657_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(
    mut v_msg_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
    mut v___y_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3669_: u8 = 0;
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3664_ = lean_ctor_get(v___y_3661_, 5);
                v___x_3665_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp_spec__0_spec__0(v_msg_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_);
                v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
                v_isSharedCheck_3674_ = (!lean_is_exclusive(v___x_3665_)) as u8;
                if v_isSharedCheck_3674_ == 0 {
                    v___x_3668_ = v___x_3665_;
                    v_isShared_3669_ = v_isSharedCheck_3674_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3666_);
                    lean_dec(v___x_3665_);
                    v___x_3668_ = lean_box(0);
                    v_isShared_3669_ = v_isSharedCheck_3674_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3664_);
                v___x_3670_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3670_, 0, v_ref_3664_);
                lean_ctor_set(v___x_3670_, 1, v_a_3666_);
                if v_isShared_3669_ == 0 {
                    lean_ctor_set_tag(v___x_3668_, 1);
                    lean_ctor_set(v___x_3668_, 0, v___x_3670_);
                    v___x_3672_ = v___x_3668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
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
    mut v_msg_3675_: *mut LeanObject,
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3681_: *mut LeanObject = core::ptr::null_mut();
    v_res_3681_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(v_msg_3675_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
    lean_dec(v___y_3679_);
    lean_dec_ref(v___y_3678_);
    lean_dec(v___y_3677_);
    lean_dec_ref(v___y_3676_);
    return v_res_3681_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(
    mut v_ref_3682_: *mut LeanObject,
    mut v_msg_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3703_: u8 = 0;
    let mut v_cancelTk_x3f_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3705_: u8 = 0;
    let mut v_inheritedTraceOptions_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3691_ = lean_ctor_get(v___y_3688_, 0);
    v_fileMap_3692_ = lean_ctor_get(v___y_3688_, 1);
    v_options_3693_ = lean_ctor_get(v___y_3688_, 2);
    v_currRecDepth_3694_ = lean_ctor_get(v___y_3688_, 3);
    v_maxRecDepth_3695_ = lean_ctor_get(v___y_3688_, 4);
    v_ref_3696_ = lean_ctor_get(v___y_3688_, 5);
    v_currNamespace_3697_ = lean_ctor_get(v___y_3688_, 6);
    v_openDecls_3698_ = lean_ctor_get(v___y_3688_, 7);
    v_initHeartbeats_3699_ = lean_ctor_get(v___y_3688_, 8);
    v_maxHeartbeats_3700_ = lean_ctor_get(v___y_3688_, 9);
    v_quotContext_3701_ = lean_ctor_get(v___y_3688_, 10);
    v_currMacroScope_3702_ = lean_ctor_get(v___y_3688_, 11);
    v_diag_3703_ = lean_ctor_get_uint8(
        v___y_3688_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3704_ = lean_ctor_get(v___y_3688_, 12);
    v_suppressElabErrors_3705_ = lean_ctor_get_uint8(
        v___y_3688_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3706_ = lean_ctor_get(v___y_3688_, 13);
    v_ref_3707_ = l_Lean_replaceRef(v_ref_3682_, v_ref_3696_);
    lean_inc_ref(v_inheritedTraceOptions_3706_);
    lean_inc(v_cancelTk_x3f_3704_);
    lean_inc(v_currMacroScope_3702_);
    lean_inc(v_quotContext_3701_);
    lean_inc(v_maxHeartbeats_3700_);
    lean_inc(v_initHeartbeats_3699_);
    lean_inc(v_openDecls_3698_);
    lean_inc(v_currNamespace_3697_);
    lean_inc(v_maxRecDepth_3695_);
    lean_inc(v_currRecDepth_3694_);
    lean_inc_ref(v_options_3693_);
    lean_inc_ref(v_fileMap_3692_);
    lean_inc_ref(v_fileName_3691_);
    v___x_3708_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3708_, 0, v_fileName_3691_);
    lean_ctor_set(v___x_3708_, 1, v_fileMap_3692_);
    lean_ctor_set(v___x_3708_, 2, v_options_3693_);
    lean_ctor_set(v___x_3708_, 3, v_currRecDepth_3694_);
    lean_ctor_set(v___x_3708_, 4, v_maxRecDepth_3695_);
    lean_ctor_set(v___x_3708_, 5, v_ref_3707_);
    lean_ctor_set(v___x_3708_, 6, v_currNamespace_3697_);
    lean_ctor_set(v___x_3708_, 7, v_openDecls_3698_);
    lean_ctor_set(v___x_3708_, 8, v_initHeartbeats_3699_);
    lean_ctor_set(v___x_3708_, 9, v_maxHeartbeats_3700_);
    lean_ctor_set(v___x_3708_, 10, v_quotContext_3701_);
    lean_ctor_set(v___x_3708_, 11, v_currMacroScope_3702_);
    lean_ctor_set(v___x_3708_, 12, v_cancelTk_x3f_3704_);
    lean_ctor_set(v___x_3708_, 13, v_inheritedTraceOptions_3706_);
    lean_ctor_set_uint8(
        v___x_3708_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3703_,
    );
    lean_ctor_set_uint8(
        v___x_3708_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3705_,
    );
    v___x_3709_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(v_msg_3683_, v___y_3686_, v___y_3687_, v___x_3708_, v___y_3689_);
    lean_dec_ref_known(v___x_3708_, 14);
    return v___x_3709_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg___boxed(
    mut v_ref_3710_: *mut LeanObject,
    mut v_msg_3711_: *mut LeanObject,
    mut v___y_3712_: *mut LeanObject,
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
    mut v___y_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
    mut v___y_3718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3719_: *mut LeanObject = core::ptr::null_mut();
    v_res_3719_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(v_ref_3710_, v_msg_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
    lean_dec(v___y_3717_);
    lean_dec_ref(v___y_3716_);
    lean_dec(v___y_3715_);
    lean_dec_ref(v___y_3714_);
    lean_dec(v___y_3713_);
    lean_dec(v___y_3712_);
    lean_dec(v_ref_3710_);
    return v_res_3719_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(
    mut v_ref_3720_: *mut LeanObject,
    mut v_msg_3721_: *mut LeanObject,
    mut v_declHint_3722_: *mut LeanObject,
    mut v___y_3723_: *mut LeanObject,
    mut v___y_3724_: *mut LeanObject,
    mut v___y_3725_: *mut LeanObject,
    mut v___y_3726_: *mut LeanObject,
    mut v___y_3727_: *mut LeanObject,
    mut v___y_3728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    v___x_3730_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17(v_msg_3721_, v_declHint_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
    v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
    lean_inc(v_a_3731_);
    lean_dec_ref(v___x_3730_);
    v___x_3732_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(v_ref_3720_, v_a_3731_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
    return v___x_3732_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg___boxed(
    mut v_ref_3733_: *mut LeanObject,
    mut v_msg_3734_: *mut LeanObject,
    mut v_declHint_3735_: *mut LeanObject,
    mut v___y_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
    mut v___y_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3743_: *mut LeanObject = core::ptr::null_mut();
    v_res_3743_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(v_ref_3733_, v_msg_3734_, v_declHint_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_, v___y_3740_, v___y_3741_);
    lean_dec(v___y_3741_);
    lean_dec_ref(v___y_3740_);
    lean_dec(v___y_3739_);
    lean_dec_ref(v___y_3738_);
    lean_dec(v___y_3737_);
    lean_dec(v___y_3736_);
    lean_dec(v_ref_3733_);
    return v_res_3743_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__0;
    v___x_3746_ = l_Lean_stringToMessageData(v___x_3745_);
    return v___x_3746_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_3748_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__2;
    v___x_3749_ = l_Lean_stringToMessageData(v___x_3748_);
    return v___x_3749_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(
    mut v_ref_3750_: *mut LeanObject,
    mut v_constName_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    v___x_3759_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__1);
    v___x_3760_ = 0;
    lean_inc(v_constName_3751_);
    v___x_3761_ = l_Lean_MessageData_ofConstName(v_constName_3751_, v___x_3760_);
    v___x_3762_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3762_, 0, v___x_3759_);
    lean_ctor_set(v___x_3762_, 1, v___x_3761_);
    v___x_3763_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___closed__3);
    v___x_3764_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3764_, 0, v___x_3762_);
    lean_ctor_set(v___x_3764_, 1, v___x_3763_);
    v___x_3765_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(v_ref_3750_, v___x_3764_, v_constName_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
    return v___x_3765_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg___boxed(
    mut v_ref_3766_: *mut LeanObject,
    mut v_constName_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
    mut v___y_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
    mut v___y_3771_: *mut LeanObject,
    mut v___y_3772_: *mut LeanObject,
    mut v___y_3773_: *mut LeanObject,
    mut v___y_3774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3775_: *mut LeanObject = core::ptr::null_mut();
    v_res_3775_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(v_ref_3766_, v_constName_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
    lean_dec(v___y_3773_);
    lean_dec_ref(v___y_3772_);
    lean_dec(v___y_3771_);
    lean_dec_ref(v___y_3770_);
    lean_dec(v___y_3769_);
    lean_dec(v___y_3768_);
    lean_dec(v_ref_3766_);
    return v_res_3775_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(
    mut v_constName_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
    mut v___y_3782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3784_ = lean_ctor_get(v___y_3781_, 5);
    v___x_3785_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(v_ref_3784_, v_constName_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
    return v___x_3785_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_constName_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
    mut v___y_3788_: *mut LeanObject,
    mut v___y_3789_: *mut LeanObject,
    mut v___y_3790_: *mut LeanObject,
    mut v___y_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
    mut v___y_3793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3794_: *mut LeanObject = core::ptr::null_mut();
    v_res_3794_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(v_constName_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
    lean_dec(v___y_3792_);
    lean_dec_ref(v___y_3791_);
    lean_dec(v___y_3790_);
    lean_dec_ref(v___y_3789_);
    lean_dec(v___y_3788_);
    lean_dec(v___y_3787_);
    return v_res_3794_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(
    mut v_constName_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
    mut v___y_3799_: *mut LeanObject,
    mut v___y_3800_: *mut LeanObject,
    mut v___y_3801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3803_ = lean_st_ref_get(v___y_3801_);
                v_env_3804_ = lean_ctor_get(v___x_3803_, 0);
                lean_inc_ref(v_env_3804_);
                lean_dec(v___x_3803_);
                v___x_3805_ = 0;
                lean_inc(v_constName_3795_);
                v___x_3806_ =
                    l_Lean_Environment_find_x3f(v_env_3804_, v_constName_3795_, v___x_3805_);
                if lean_obj_tag(v___x_3806_) == 0 {
                    v___x_3807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(v_constName_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
                    return v___x_3807_;
                } else {
                    lean_dec(v_constName_3795_);
                    v_val_3808_ = lean_ctor_get(v___x_3806_, 0);
                    v_isSharedCheck_3815_ = (!lean_is_exclusive(v___x_3806_)) as u8;
                    if v_isSharedCheck_3815_ == 0 {
                        v___x_3810_ = v___x_3806_;
                        v_isShared_3811_ = v_isSharedCheck_3815_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3808_);
                        lean_dec(v___x_3806_);
                        v___x_3810_ = lean_box(0);
                        v_isShared_3811_ = v_isSharedCheck_3815_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3811_ == 0 {
                    lean_ctor_set_tag(v___x_3810_, 0);
                    v___x_3813_ = v___x_3810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_val_3808_);
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
    mut v_constName_3816_: *mut LeanObject,
    mut v___y_3817_: *mut LeanObject,
    mut v___y_3818_: *mut LeanObject,
    mut v___y_3819_: *mut LeanObject,
    mut v___y_3820_: *mut LeanObject,
    mut v___y_3821_: *mut LeanObject,
    mut v___y_3822_: *mut LeanObject,
    mut v___y_3823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3824_: *mut LeanObject = core::ptr::null_mut();
    v_res_3824_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(v_constName_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
    lean_dec(v___y_3822_);
    lean_dec_ref(v___y_3821_);
    lean_dec(v___y_3820_);
    lean_dec_ref(v___y_3819_);
    lean_dec(v___y_3818_);
    lean_dec(v___y_3817_);
    return v_res_3824_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0()
-> *mut LeanObject {
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    v___x_3825_ = l_instMonadEIO(lean_box(0));
    return v___x_3825_;
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8(
    mut v_msg_3830_: *mut LeanObject,
    mut v___y_3831_: *mut LeanObject,
    mut v___y_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
    mut v___y_3834_: *mut LeanObject,
    mut v___y_3835_: *mut LeanObject,
    mut v___y_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v_toFunctor_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3850_: u8 = 0;
    let mut v___f_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v_toFunctor_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeq_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3874_: u8 = 0;
    let mut v___f_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_27360__overap_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_unused_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_unused_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3901_: u8 = 0;
    let mut v_unused_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_unused_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3838_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0_once), _init_l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__0);
                v___x_3839_ = l_StateRefT_x27_instMonad___redArg(v___x_3838_);
                v_toApplicative_3840_ = lean_ctor_get(v___x_3839_, 0);
                v_isSharedCheck_3903_ = (!lean_is_exclusive(v___x_3839_)) as u8;
                if v_isSharedCheck_3903_ == 0 {
                    v_unused_3904_ = lean_ctor_get(v___x_3839_, 1);
                    lean_dec(v_unused_3904_);
                    v___x_3842_ = v___x_3839_;
                    v_isShared_3843_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3840_);
                    lean_dec(v___x_3839_);
                    v___x_3842_ = lean_box(0);
                    v_isShared_3843_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_3844_ = lean_ctor_get(v_toApplicative_3840_, 0);
                v_toSeq_3845_ = lean_ctor_get(v_toApplicative_3840_, 2);
                v_toSeqLeft_3846_ = lean_ctor_get(v_toApplicative_3840_, 3);
                v_toSeqRight_3847_ = lean_ctor_get(v_toApplicative_3840_, 4);
                v_isSharedCheck_3901_ = (!lean_is_exclusive(v_toApplicative_3840_)) as u8;
                if v_isSharedCheck_3901_ == 0 {
                    v_unused_3902_ = lean_ctor_get(v_toApplicative_3840_, 1);
                    lean_dec(v_unused_3902_);
                    v___x_3849_ = v_toApplicative_3840_;
                    v_isShared_3850_ = v_isSharedCheck_3901_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3847_);
                    lean_inc(v_toSeqLeft_3846_);
                    lean_inc(v_toSeq_3845_);
                    lean_inc(v_toFunctor_3844_);
                    lean_dec(v_toApplicative_3840_);
                    v___x_3849_ = lean_box(0);
                    v_isShared_3850_ = v_isSharedCheck_3901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_3851_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__1;
                v___f_3852_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__2;
                lean_inc_ref(v_toFunctor_3844_);
                v___f_3853_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3853_, 0, v_toFunctor_3844_);
                v___f_3854_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3854_, 0, v_toFunctor_3844_);
                v___x_3855_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3855_, 0, v___f_3853_);
                lean_ctor_set(v___x_3855_, 1, v___f_3854_);
                v___f_3856_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3856_, 0, v_toSeqRight_3847_);
                v___f_3857_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3857_, 0, v_toSeqLeft_3846_);
                v___f_3858_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3858_, 0, v_toSeq_3845_);
                if v_isShared_3850_ == 0 {
                    lean_ctor_set(v___x_3849_, 4, v___f_3856_);
                    lean_ctor_set(v___x_3849_, 3, v___f_3857_);
                    lean_ctor_set(v___x_3849_, 2, v___f_3858_);
                    lean_ctor_set(v___x_3849_, 1, v___f_3851_);
                    lean_ctor_set(v___x_3849_, 0, v___x_3855_);
                    v___x_3860_ = v___x_3849_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3900_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3855_);
                    lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___f_3851_);
                    lean_ctor_set(v_reuseFailAlloc_3900_, 2, v___f_3858_);
                    lean_ctor_set(v_reuseFailAlloc_3900_, 3, v___f_3857_);
                    lean_ctor_set(v_reuseFailAlloc_3900_, 4, v___f_3856_);
                    v___x_3860_ = v_reuseFailAlloc_3900_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3843_ == 0 {
                    lean_ctor_set(v___x_3842_, 1, v___f_3852_);
                    lean_ctor_set(v___x_3842_, 0, v___x_3860_);
                    v___x_3862_ = v___x_3842_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3860_);
                    lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___f_3852_);
                    v___x_3862_ = v_reuseFailAlloc_3899_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3863_ = l_StateRefT_x27_instMonad___redArg(v___x_3862_);
                v_toApplicative_3864_ = lean_ctor_get(v___x_3863_, 0);
                v_isSharedCheck_3897_ = (!lean_is_exclusive(v___x_3863_)) as u8;
                if v_isSharedCheck_3897_ == 0 {
                    v_unused_3898_ = lean_ctor_get(v___x_3863_, 1);
                    lean_dec(v_unused_3898_);
                    v___x_3866_ = v___x_3863_;
                    v_isShared_3867_ = v_isSharedCheck_3897_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_toApplicative_3864_);
                    lean_dec(v___x_3863_);
                    v___x_3866_ = lean_box(0);
                    v_isShared_3867_ = v_isSharedCheck_3897_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_toFunctor_3868_ = lean_ctor_get(v_toApplicative_3864_, 0);
                v_toSeq_3869_ = lean_ctor_get(v_toApplicative_3864_, 2);
                v_toSeqLeft_3870_ = lean_ctor_get(v_toApplicative_3864_, 3);
                v_toSeqRight_3871_ = lean_ctor_get(v_toApplicative_3864_, 4);
                v_isSharedCheck_3895_ = (!lean_is_exclusive(v_toApplicative_3864_)) as u8;
                if v_isSharedCheck_3895_ == 0 {
                    v_unused_3896_ = lean_ctor_get(v_toApplicative_3864_, 1);
                    lean_dec(v_unused_3896_);
                    v___x_3873_ = v_toApplicative_3864_;
                    v_isShared_3874_ = v_isSharedCheck_3895_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_toSeqRight_3871_);
                    lean_inc(v_toSeqLeft_3870_);
                    lean_inc(v_toSeq_3869_);
                    lean_inc(v_toFunctor_3868_);
                    lean_dec(v_toApplicative_3864_);
                    v___x_3873_ = lean_box(0);
                    v_isShared_3874_ = v_isSharedCheck_3895_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___f_3875_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__3;
                v___f_3876_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___closed__4;
                lean_inc_ref(v_toFunctor_3868_);
                v___f_3877_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3877_, 0, v_toFunctor_3868_);
                v___f_3878_ = lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3878_, 0, v_toFunctor_3868_);
                v___x_3879_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3879_, 0, v___f_3877_);
                lean_ctor_set(v___x_3879_, 1, v___f_3878_);
                v___f_3880_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3880_, 0, v_toSeqRight_3871_);
                v___f_3881_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3881_, 0, v_toSeqLeft_3870_);
                v___f_3882_ = lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                lean_closure_set(v___f_3882_, 0, v_toSeq_3869_);
                if v_isShared_3874_ == 0 {
                    lean_ctor_set(v___x_3873_, 4, v___f_3880_);
                    lean_ctor_set(v___x_3873_, 3, v___f_3881_);
                    lean_ctor_set(v___x_3873_, 2, v___f_3882_);
                    lean_ctor_set(v___x_3873_, 1, v___f_3875_);
                    lean_ctor_set(v___x_3873_, 0, v___x_3879_);
                    v___x_3884_ = v___x_3873_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3879_);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 1, v___f_3875_);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 2, v___f_3882_);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 3, v___f_3881_);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 4, v___f_3880_);
                    v___x_3884_ = v_reuseFailAlloc_3894_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3867_ == 0 {
                    lean_ctor_set(v___x_3866_, 1, v___f_3876_);
                    lean_ctor_set(v___x_3866_, 0, v___x_3884_);
                    v___x_3886_ = v___x_3866_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3884_);
                    lean_ctor_set(v_reuseFailAlloc_3893_, 1, v___f_3876_);
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
                lean_dec(v___x_3890_);
                lean_inc(v___y_3836_);
                lean_inc_ref(v___y_3835_);
                lean_inc(v___y_3834_);
                lean_inc_ref(v___y_3833_);
                lean_inc(v___y_3832_);
                lean_inc(v___y_3831_);
                v___x_3892_ = lean_apply_7(
                    v___x_27360__overap_3891_,
                    v___y_3831_,
                    v___y_3832_,
                    v___y_3833_,
                    v___y_3834_,
                    v___y_3835_,
                    v___y_3836_,
                    lean_box(0),
                );
                return v___x_3892_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8___boxed(
    mut v_msg_3905_: *mut LeanObject,
    mut v___y_3906_: *mut LeanObject,
    mut v___y_3907_: *mut LeanObject,
    mut v___y_3908_: *mut LeanObject,
    mut v___y_3909_: *mut LeanObject,
    mut v___y_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3913_: *mut LeanObject = core::ptr::null_mut();
    v_res_3913_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8(v_msg_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
    lean_dec(v___y_3911_);
    lean_dec_ref(v___y_3910_);
    lean_dec(v___y_3909_);
    lean_dec_ref(v___y_3908_);
    lean_dec(v___y_3907_);
    lean_dec(v___y_3906_);
    return v_res_3913_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3()
-> *mut LeanObject {
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    v___x_3917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__2;
    v___x_3918_ = lean_unsigned_to_nat(53);
    v___x_3919_ = lean_unsigned_to_nat(62);
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
    mut v_bs_3925_: *mut LeanObject,
    mut v___y_3926_: *mut LeanObject,
    mut v___y_3927_: *mut LeanObject,
    mut v___y_3928_: *mut LeanObject,
    mut v___y_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
    mut v___y_3931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3933_: u8 = 0;
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: usize = 0;
    let mut v___x_3943_: usize = 0;
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numFields_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: u8 = 0;
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3933_ = lean_usize_dec_lt(v_i_3924_, v_sz_3923_);
                if v___x_3933_ == 0 {
                    v___x_3934_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3934_, 0, v_bs_3925_);
                    return v___x_3934_;
                } else {
                    v_v_3935_ = lean_array_uget_borrowed(v_bs_3925_, v_i_3924_);
                    lean_inc(v_v_3935_);
                    v___x_3936_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(v_v_3935_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
                    if lean_obj_tag(v___x_3936_) == 0 {
                        v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
                        lean_inc(v_a_3937_);
                        lean_dec_ref_known(v___x_3936_, 1);
                        v___x_3938_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3939_ = lean_array_uset(v_bs_3925_, v_i_3924_, v___x_3938_);
                        if lean_obj_tag(v_a_3937_) == 6 {
                            v_val_3946_ = lean_ctor_get(v_a_3937_, 0);
                            lean_inc_ref(v_val_3946_);
                            lean_dec_ref_known(v_a_3937_, 1);
                            v_numFields_3947_ = lean_ctor_get(v_val_3946_, 4);
                            lean_inc(v_numFields_3947_);
                            lean_dec_ref(v_val_3946_);
                            v___x_3948_ = 0;
                            v___x_3949_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v___x_3949_, 0, v_numFields_3947_);
                            lean_ctor_set(v___x_3949_, 1, v___x_3938_);
                            lean_ctor_set_uint8(
                                v___x_3949_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v___x_3948_,
                            );
                            v_a_3941_ = v___x_3949_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_3937_);
                            v___x_3950_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10___closed__3);
                            v___x_3951_ = l_panic___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__8(v___x_3950_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
                            if lean_obj_tag(v___x_3951_) == 0 {
                                v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
                                lean_inc(v_a_3952_);
                                lean_dec_ref_known(v___x_3951_, 1);
                                v_a_3941_ = v_a_3952_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_bs_x27_3939_);
                                v_a_3953_ = lean_ctor_get(v___x_3951_, 0);
                                v_isSharedCheck_3960_ = (!lean_is_exclusive(v___x_3951_)) as u8;
                                if v_isSharedCheck_3960_ == 0 {
                                    v___x_3955_ = v___x_3951_;
                                    v_isShared_3956_ = v_isSharedCheck_3960_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3953_);
                                    lean_dec(v___x_3951_);
                                    v___x_3955_ = lean_box(0);
                                    v_isShared_3956_ = v_isSharedCheck_3960_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_bs_3925_);
                        v_a_3961_ = lean_ctor_get(v___x_3936_, 0);
                        v_isSharedCheck_3968_ = (!lean_is_exclusive(v___x_3936_)) as u8;
                        if v_isSharedCheck_3968_ == 0 {
                            v___x_3963_ = v___x_3936_;
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3961_);
                            lean_dec(v___x_3936_);
                            v___x_3963_ = lean_box(0);
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
                    v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
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
                    v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
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
    mut v_sz_3969_: *mut LeanObject,
    mut v_i_3970_: *mut LeanObject,
    mut v_bs_3971_: *mut LeanObject,
    mut v___y_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
    mut v___y_3974_: *mut LeanObject,
    mut v___y_3975_: *mut LeanObject,
    mut v___y_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3979_: usize = 0;
    let mut v_i_boxed_3980_: usize = 0;
    let mut v_res_3981_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3979_ = lean_unbox_usize(v_sz_3969_);
    lean_dec(v_sz_3969_);
    v_i_boxed_3980_ = lean_unbox_usize(v_i_3970_);
    lean_dec(v_i_3970_);
    v_res_3981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__10(v_sz_boxed_3979_, v_i_boxed_3980_, v_bs_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
    lean_dec(v___y_3977_);
    lean_dec_ref(v___y_3976_);
    lean_dec(v___y_3975_);
    lean_dec_ref(v___y_3974_);
    lean_dec(v___y_3973_);
    lean_dec(v___y_3972_);
    return v_res_3981_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(
    mut v_declName_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    v___x_3985_ = lean_st_ref_get(v___y_3983_);
    v_env_3986_ = lean_ctor_get(v___x_3985_, 0);
    lean_inc_ref(v_env_3986_);
    lean_dec(v___x_3985_);
    v___x_3987_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_3986_, v_declName_3982_);
    v___x_3988_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3988_, 0, v___x_3987_);
    return v___x_3988_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg___boxed(
    mut v_declName_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
    mut v___y_3991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3992_: *mut LeanObject = core::ptr::null_mut();
    v_res_3992_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(v_declName_3989_, v___y_3990_);
    lean_dec(v___y_3990_);
    return v_res_3992_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    v___x_3993_ = lean_box(0);
    v___x_3994_ = lean_unsigned_to_nat(16);
    v___x_3995_ = lean_mk_array(v___x_3994_, v___x_3993_);
    return v___x_3995_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1()
-> *mut LeanObject {
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    v___x_3996_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__0);
    v___x_3997_ = lean_unsigned_to_nat(0);
    v___x_3998_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3998_, 0, v___x_3997_);
    lean_ctor_set(v___x_3998_, 1, v___x_3996_);
    return v___x_3998_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5(
    mut v_e_4001_: *mut LeanObject,
    mut v_alsoCasesOn_4002_: u8,
    mut v___y_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
    mut v___y_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v_val_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v_dummy_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: u8 = 0;
    let mut v_numParams_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4066_: u8 = 0;
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    let mut v_indName_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4075_: u8 = 0;
    let mut v_val_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4079_: u8 = 0;
    let mut v_toConstantVal_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4114_: usize = 0;
    let mut v___x_4115_: usize = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v_start_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut v_a_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4145_: u8 = 0;
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4149_: u8 = 0;
    let mut v_lower_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: u8 = 0;
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: u8 = 0;
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4165_: u8 = 0;
    let mut v_a_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4173_: u8 = 0;
    let mut v_isSharedCheck_4174_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4013_ = l_Lean_Expr_isApp(v_e_4001_);
                if v___x_4013_ == 0 {
                    lean_dec_ref(v_e_4001_);
                    v___x_4014_ = lean_box(0);
                    v___x_4015_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4015_, 0, v___x_4014_);
                    return v___x_4015_;
                } else {
                    v___x_4016_ = l_Lean_Expr_getAppFn(v_e_4001_);
                    if lean_obj_tag(v___x_4016_) == 4 {
                        v_declName_4017_ = lean_ctor_get(v___x_4016_, 0);
                        lean_inc_n(v_declName_4017_, 2);
                        v_us_4018_ = lean_ctor_get(v___x_4016_, 1);
                        lean_inc(v_us_4018_);
                        lean_dec_ref_known(v___x_4016_, 2);
                        v___x_4019_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(v_declName_4017_, v___y_4008_);
                        v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
                        v_isSharedCheck_4174_ = (!lean_is_exclusive(v___x_4019_)) as u8;
                        if v_isSharedCheck_4174_ == 0 {
                            v___x_4022_ = v___x_4019_;
                            v_isShared_4023_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4020_);
                            lean_dec(v___x_4019_);
                            v___x_4022_ = lean_box(0);
                            v_isShared_4023_ = v_isSharedCheck_4174_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_4016_);
                        lean_dec_ref(v_e_4001_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4011_ = lean_box(0);
                v___x_4012_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4012_, 0, v___x_4011_);
                return v___x_4012_;
            }
            2 => {
                if lean_obj_tag(v_a_4020_) == 1 {
                    v_val_4024_ = lean_ctor_get(v_a_4020_, 0);
                    v_isSharedCheck_4066_ = (!lean_is_exclusive(v_a_4020_)) as u8;
                    if v_isSharedCheck_4066_ == 0 {
                        v___x_4026_ = v_a_4020_;
                        v_isShared_4027_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_4024_);
                        lean_dec(v_a_4020_);
                        v___x_4026_ = lean_box(0);
                        v_isShared_4027_ = v_isSharedCheck_4066_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4022_);
                    lean_dec(v_a_4020_);
                    v___x_4067_ = lean_st_ref_get(v___y_4008_);
                    if v_alsoCasesOn_4002_ == 0 {
                        lean_dec(v___x_4067_);
                        lean_dec(v_us_4018_);
                        lean_dec(v_declName_4017_);
                        lean_dec_ref(v_e_4001_);
                        state = 1;
                        continue;
                    } else {
                        v_env_4068_ = lean_ctor_get(v___x_4067_, 0);
                        lean_inc_ref(v_env_4068_);
                        lean_dec(v___x_4067_);
                        lean_inc(v_declName_4017_);
                        v___x_4069_ = l_Lean_isCasesOnRecursor(v_env_4068_, v_declName_4017_);
                        if v___x_4069_ == 0 {
                            lean_dec(v_us_4018_);
                            lean_dec(v_declName_4017_);
                            lean_dec_ref(v_e_4001_);
                            state = 1;
                            continue;
                        } else {
                            v_indName_4070_ = l_Lean_Name_getPrefix(v_declName_4017_);
                            v___x_4071_ = l_Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7(v_indName_4070_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
                            if lean_obj_tag(v___x_4071_) == 0 {
                                v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
                                v_isSharedCheck_4165_ = (!lean_is_exclusive(v___x_4071_)) as u8;
                                if v_isSharedCheck_4165_ == 0 {
                                    v___x_4074_ = v___x_4071_;
                                    v_isShared_4075_ = v_isSharedCheck_4165_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4072_);
                                    lean_dec(v___x_4071_);
                                    v___x_4074_ = lean_box(0);
                                    v_isShared_4075_ = v_isSharedCheck_4165_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v_us_4018_);
                                lean_dec(v_declName_4017_);
                                lean_dec_ref(v_e_4001_);
                                v_a_4166_ = lean_ctor_get(v___x_4071_, 0);
                                v_isSharedCheck_4173_ = (!lean_is_exclusive(v___x_4071_)) as u8;
                                if v_isSharedCheck_4173_ == 0 {
                                    v___x_4168_ = v___x_4071_;
                                    v_isShared_4169_ = v_isSharedCheck_4173_;
                                    state = 18;
                                    continue;
                                } else {
                                    lean_inc(v_a_4166_);
                                    lean_dec(v___x_4071_);
                                    v___x_4168_ = lean_box(0);
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
                v_dummy_4028_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                v_nargs_4029_ = l_Lean_Expr_getAppNumArgs(v_e_4001_);
                lean_inc(v_nargs_4029_);
                v___x_4030_ = lean_mk_array(v_nargs_4029_, v_dummy_4028_);
                v___x_4031_ = lean_unsigned_to_nat(1);
                v___x_4032_ = lean_nat_sub(v_nargs_4029_, v___x_4031_);
                lean_dec(v_nargs_4029_);
                v_args_4033_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_4001_,
                    v___x_4030_,
                    v___x_4032_,
                );
                v___x_4034_ = lean_array_get_size(v_args_4033_);
                v___x_4035_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_4024_);
                v___x_4036_ = lean_nat_dec_lt(v___x_4034_, v___x_4035_);
                lean_dec(v___x_4035_);
                if v___x_4036_ == 0 {
                    v_numParams_4037_ = lean_ctor_get(v_val_4024_, 0);
                    v_numDiscrs_4038_ = lean_ctor_get(v_val_4024_, 1);
                    v___x_4039_ = lean_array_mk(v_us_4018_);
                    v___x_4040_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_4037_);
                    v___x_4041_ =
                        l_Array_extract___redArg(v_args_4033_, v___x_4040_, v_numParams_4037_);
                    v___x_4042_ = l_Lean_instInhabitedExpr;
                    v___x_4043_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_4024_);
                    v___x_4044_ = lean_array_get(v___x_4042_, v_args_4033_, v___x_4043_);
                    lean_dec(v___x_4043_);
                    v___x_4045_ = lean_nat_add(v_numParams_4037_, v___x_4031_);
                    v___x_4046_ = lean_nat_add(v___x_4045_, v_numDiscrs_4038_);
                    lean_inc(v___x_4046_);
                    lean_inc_ref_n(v_args_4033_, 2);
                    v___x_4047_ =
                        l_Array_toSubarray___redArg(v_args_4033_, v___x_4045_, v___x_4046_);
                    v___x_4048_ = l_Subarray_copy___redArg(v___x_4047_);
                    v___x_4049_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_4024_);
                    v___x_4050_ = lean_nat_add(v___x_4046_, v___x_4049_);
                    lean_dec(v___x_4049_);
                    lean_inc(v___x_4050_);
                    v___x_4051_ =
                        l_Array_toSubarray___redArg(v_args_4033_, v___x_4046_, v___x_4050_);
                    v___x_4052_ = l_Subarray_copy___redArg(v___x_4051_);
                    v___x_4053_ =
                        l_Array_toSubarray___redArg(v_args_4033_, v___x_4050_, v___x_4034_);
                    v___x_4054_ = l_Subarray_copy___redArg(v___x_4053_);
                    v___x_4055_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_4055_, 0, v_val_4024_);
                    lean_ctor_set(v___x_4055_, 1, v_declName_4017_);
                    lean_ctor_set(v___x_4055_, 2, v___x_4039_);
                    lean_ctor_set(v___x_4055_, 3, v___x_4041_);
                    lean_ctor_set(v___x_4055_, 4, v___x_4044_);
                    lean_ctor_set(v___x_4055_, 5, v___x_4048_);
                    lean_ctor_set(v___x_4055_, 6, v___x_4052_);
                    lean_ctor_set(v___x_4055_, 7, v___x_4054_);
                    if v_isShared_4027_ == 0 {
                        lean_ctor_set(v___x_4026_, 0, v___x_4055_);
                        v___x_4057_ = v___x_4026_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4061_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4061_, 0, v___x_4055_);
                        v___x_4057_ = v_reuseFailAlloc_4061_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_4033_);
                    lean_del_object(v___x_4026_);
                    lean_dec(v_val_4024_);
                    lean_dec(v_us_4018_);
                    lean_dec(v_declName_4017_);
                    v___x_4062_ = lean_box(0);
                    if v_isShared_4023_ == 0 {
                        lean_ctor_set(v___x_4022_, 0, v___x_4062_);
                        v___x_4064_ = v___x_4022_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
                        v___x_4064_ = v_reuseFailAlloc_4065_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4023_ == 0 {
                    lean_ctor_set(v___x_4022_, 0, v___x_4057_);
                    v___x_4059_ = v___x_4022_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4057_);
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
                if lean_obj_tag(v_a_4072_) == 5 {
                    v_val_4076_ = lean_ctor_get(v_a_4072_, 0);
                    v_isSharedCheck_4160_ = (!lean_is_exclusive(v_a_4072_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4078_ = v_a_4072_;
                        v_isShared_4079_ = v_isSharedCheck_4160_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_4076_);
                        lean_dec(v_a_4072_);
                        v___x_4078_ = lean_box(0);
                        v_isShared_4079_ = v_isSharedCheck_4160_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4072_);
                    lean_dec(v_us_4018_);
                    lean_dec(v_declName_4017_);
                    lean_dec_ref(v_e_4001_);
                    v___x_4161_ = lean_box(0);
                    if v_isShared_4075_ == 0 {
                        lean_ctor_set(v___x_4074_, 0, v___x_4161_);
                        v___x_4163_ = v___x_4074_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4161_);
                        v___x_4163_ = v_reuseFailAlloc_4164_;
                        state = 17;
                        continue;
                    }
                }
            }
            8 => {
                v_toConstantVal_4080_ = lean_ctor_get(v_val_4076_, 0);
                lean_inc_ref(v_toConstantVal_4080_);
                v_numParams_4081_ = lean_ctor_get(v_val_4076_, 1);
                lean_inc(v_numParams_4081_);
                v_numIndices_4082_ = lean_ctor_get(v_val_4076_, 2);
                lean_inc(v_numIndices_4082_);
                v_ctors_4083_ = lean_ctor_get(v_val_4076_, 4);
                lean_inc(v_ctors_4083_);
                v_nargs_4084_ = l_Lean_Expr_getAppNumArgs(v_e_4001_);
                v_dummy_4085_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                lean_inc(v_nargs_4084_);
                v___x_4086_ = lean_mk_array(v_nargs_4084_, v_dummy_4085_);
                v___x_4087_ = lean_unsigned_to_nat(1);
                v___x_4088_ = lean_nat_sub(v_nargs_4084_, v___x_4087_);
                lean_dec(v_nargs_4084_);
                v_args_4089_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_4001_,
                    v___x_4086_,
                    v___x_4088_,
                );
                v___x_4090_ = lean_nat_add(v_numParams_4081_, v___x_4087_);
                v___x_4091_ = lean_nat_add(v___x_4090_, v_numIndices_4082_);
                v___x_4092_ = lean_nat_add(v___x_4091_, v___x_4087_);
                lean_dec(v___x_4091_);
                v___x_4093_ = l_Lean_InductiveVal_numCtors(v_val_4076_);
                lean_dec_ref(v_val_4076_);
                v___x_4094_ = lean_nat_add(v___x_4092_, v___x_4093_);
                lean_dec(v___x_4093_);
                v___x_4095_ = lean_array_get_size(v_args_4089_);
                v___x_4096_ = lean_nat_dec_le(v___x_4094_, v___x_4095_);
                if v___x_4096_ == 0 {
                    lean_dec(v___x_4094_);
                    lean_dec(v___x_4092_);
                    lean_dec(v___x_4090_);
                    lean_dec_ref(v_args_4089_);
                    lean_dec(v_ctors_4083_);
                    lean_dec(v_numIndices_4082_);
                    lean_dec(v_numParams_4081_);
                    lean_dec_ref(v_toConstantVal_4080_);
                    lean_del_object(v___x_4078_);
                    lean_dec(v_us_4018_);
                    lean_dec(v_declName_4017_);
                    v___x_4097_ = lean_box(0);
                    if v_isShared_4075_ == 0 {
                        lean_ctor_set(v___x_4074_, 0, v___x_4097_);
                        v___x_4099_ = v___x_4074_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4100_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4100_, 0, v___x_4097_);
                        v___x_4099_ = v_reuseFailAlloc_4100_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4074_);
                    v___x_4101_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_4081_);
                    lean_inc_ref_n(v_args_4089_, 3);
                    v_params_4102_ =
                        l_Array_toSubarray___redArg(v_args_4089_, v___x_4101_, v_numParams_4081_);
                    v___x_4103_ = l_Lean_instInhabitedExpr;
                    v_motive_4104_ = lean_array_get(v___x_4103_, v_args_4089_, v_numParams_4081_);
                    lean_dec(v_numParams_4081_);
                    lean_inc(v___x_4092_);
                    v_discrs_4105_ =
                        l_Array_toSubarray___redArg(v_args_4089_, v___x_4090_, v___x_4092_);
                    v___x_4106_ = lean_nat_add(v_numIndices_4082_, v___x_4087_);
                    lean_dec(v_numIndices_4082_);
                    v___x_4107_ = lean_box(0);
                    v_discrInfos_4108_ = lean_mk_array(v___x_4106_, v___x_4107_);
                    lean_inc(v___x_4094_);
                    v_alts_4109_ =
                        l_Array_toSubarray___redArg(v_args_4089_, v___x_4092_, v___x_4094_);
                    v___x_4159_ = lean_nat_dec_le(v___x_4094_, v___x_4101_);
                    if v___x_4159_ == 0 {
                        v_lower_4151_ = v___x_4094_;
                        v_upper_4152_ = v___x_4095_;
                        state = 16;
                        continue;
                    } else {
                        lean_dec(v___x_4094_);
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
                if lean_obj_tag(v___x_4116_) == 0 {
                    v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
                    v_isSharedCheck_4141_ = (!lean_is_exclusive(v___x_4116_)) as u8;
                    if v_isSharedCheck_4141_ == 0 {
                        v___x_4119_ = v___x_4116_;
                        v_isShared_4120_ = v_isSharedCheck_4141_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4117_);
                        lean_dec(v___x_4116_);
                        v___x_4119_ = lean_box(0);
                        v_isShared_4120_ = v_isSharedCheck_4141_;
                        state = 11;
                        continue;
                    }
                } else {
                    lean_dec(v___y_4112_);
                    lean_dec_ref(v___y_4111_);
                    lean_dec_ref(v_alts_4109_);
                    lean_dec_ref(v_discrInfos_4108_);
                    lean_dec_ref(v_discrs_4105_);
                    lean_dec(v_motive_4104_);
                    lean_dec_ref(v_params_4102_);
                    lean_del_object(v___x_4078_);
                    lean_dec(v_us_4018_);
                    lean_dec(v_declName_4017_);
                    v_a_4142_ = lean_ctor_get(v___x_4116_, 0);
                    v_isSharedCheck_4149_ = (!lean_is_exclusive(v___x_4116_)) as u8;
                    if v_isSharedCheck_4149_ == 0 {
                        v___x_4144_ = v___x_4116_;
                        v_isShared_4145_ = v_isSharedCheck_4149_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_4142_);
                        lean_dec(v___x_4116_);
                        v___x_4144_ = lean_box(0);
                        v_isShared_4145_ = v_isSharedCheck_4149_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                v_start_4121_ = lean_ctor_get(v_params_4102_, 1);
                lean_inc(v_start_4121_);
                v_stop_4122_ = lean_ctor_get(v_params_4102_, 2);
                lean_inc(v_stop_4122_);
                v_start_4123_ = lean_ctor_get(v_discrs_4105_, 1);
                lean_inc(v_start_4123_);
                v_stop_4124_ = lean_ctor_get(v_discrs_4105_, 2);
                lean_inc(v_stop_4124_);
                v___x_4125_ = lean_nat_sub(v_stop_4122_, v_start_4121_);
                lean_dec(v_start_4121_);
                lean_dec(v_stop_4122_);
                v___x_4126_ = lean_nat_sub(v_stop_4124_, v_start_4123_);
                lean_dec(v_start_4123_);
                lean_dec(v_stop_4124_);
                v___x_4127_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1_once), _init_l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5___closed__1);
                v___x_4128_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_4128_, 0, v___x_4125_);
                lean_ctor_set(v___x_4128_, 1, v___x_4126_);
                lean_ctor_set(v___x_4128_, 2, v_a_4117_);
                lean_ctor_set(v___x_4128_, 3, v___y_4112_);
                lean_ctor_set(v___x_4128_, 4, v_discrInfos_4108_);
                lean_ctor_set(v___x_4128_, 5, v___x_4127_);
                v___x_4129_ = lean_array_mk(v_us_4018_);
                v___x_4130_ = l_Subarray_copy___redArg(v_params_4102_);
                v___x_4131_ = l_Subarray_copy___redArg(v_discrs_4105_);
                v___x_4132_ = l_Subarray_copy___redArg(v_alts_4109_);
                v___x_4133_ = l_Subarray_copy___redArg(v___y_4111_);
                v___x_4134_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_4134_, 0, v___x_4128_);
                lean_ctor_set(v___x_4134_, 1, v_declName_4017_);
                lean_ctor_set(v___x_4134_, 2, v___x_4129_);
                lean_ctor_set(v___x_4134_, 3, v___x_4130_);
                lean_ctor_set(v___x_4134_, 4, v_motive_4104_);
                lean_ctor_set(v___x_4134_, 5, v___x_4131_);
                lean_ctor_set(v___x_4134_, 6, v___x_4132_);
                lean_ctor_set(v___x_4134_, 7, v___x_4133_);
                if v_isShared_4079_ == 0 {
                    lean_ctor_set_tag(v___x_4078_, 1);
                    lean_ctor_set(v___x_4078_, 0, v___x_4134_);
                    v___x_4136_ = v___x_4078_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4140_, 0, v___x_4134_);
                    v___x_4136_ = v_reuseFailAlloc_4140_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_4120_ == 0 {
                    lean_ctor_set(v___x_4119_, 0, v___x_4136_);
                    v___x_4138_ = v___x_4119_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
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
                    v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
                    v___x_4147_ = v_reuseFailAlloc_4148_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4147_;
            }
            16 => {
                v_levelParams_4153_ = lean_ctor_get(v_toConstantVal_4080_, 1);
                lean_inc(v_levelParams_4153_);
                lean_dec_ref(v_toConstantVal_4080_);
                v___x_4154_ =
                    l_Array_toSubarray___redArg(v_args_4089_, v_lower_4151_, v_upper_4152_);
                v___x_4155_ = l_List_lengthTR___redArg(v_levelParams_4153_);
                lean_dec(v_levelParams_4153_);
                v___x_4156_ = l_List_lengthTR___redArg(v_us_4018_);
                v___x_4157_ = lean_nat_dec_eq(v___x_4155_, v___x_4156_);
                lean_dec(v___x_4156_);
                lean_dec(v___x_4155_);
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
                    v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
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
    mut v_e_4175_: *mut LeanObject,
    mut v_alsoCasesOn_4176_: *mut LeanObject,
    mut v___y_4177_: *mut LeanObject,
    mut v___y_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
    mut v___y_4180_: *mut LeanObject,
    mut v___y_4181_: *mut LeanObject,
    mut v___y_4182_: *mut LeanObject,
    mut v___y_4183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_alsoCasesOn_boxed_4184_: u8 = 0;
    let mut v_res_4185_: *mut LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_4184_ = (lean_unbox(v_alsoCasesOn_4176_) as u8);
    v_res_4185_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5(v_e_4175_, v_alsoCasesOn_boxed_4184_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
    lean_dec(v___y_4182_);
    lean_dec_ref(v___y_4181_);
    lean_dec(v___y_4180_);
    lean_dec_ref(v___y_4179_);
    lean_dec(v___y_4178_);
    lean_dec(v___y_4177_);
    return v_res_4185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0(
    mut v_recArgInfos_4186_: *mut LeanObject,
    mut v_positions_4187_: *mut LeanObject,
    mut v_params_4188_: *mut LeanObject,
    mut v_recFnNames_4189_: *mut LeanObject,
    mut v_containsRecFn_4190_: *mut LeanObject,
    mut v_ctx_4191_: *mut LeanObject,
    mut v_sz_4192_: usize,
    mut v_i_4193_: usize,
    mut v_bs_4194_: *mut LeanObject,
    mut v___y_4195_: *mut LeanObject,
    mut v___y_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4202_: u8 = 0;
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: usize = 0;
    let mut v___x_4210_: usize = 0;
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4202_ = lean_usize_dec_lt(v_i_4193_, v_sz_4192_);
                if v___x_4202_ == 0 {
                    lean_dec_ref(v_ctx_4191_);
                    lean_dec_ref(v_containsRecFn_4190_);
                    lean_dec_ref(v_recFnNames_4189_);
                    lean_dec_ref(v_params_4188_);
                    lean_dec_ref(v_positions_4187_);
                    lean_dec_ref(v_recArgInfos_4186_);
                    v___x_4203_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4203_, 0, v_bs_4194_);
                    return v___x_4203_;
                } else {
                    v_v_4204_ = lean_array_uget_borrowed(v_bs_4194_, v_i_4193_);
                    lean_inc_ref(v___y_4199_);
                    lean_inc(v_v_4204_);
                    lean_inc_ref(v_ctx_4191_);
                    lean_inc_ref(v_containsRecFn_4190_);
                    lean_inc_ref(v_recFnNames_4189_);
                    lean_inc_ref(v_params_4188_);
                    lean_inc_ref(v_positions_4187_);
                    lean_inc_ref(v_recArgInfos_4186_);
                    v___x_4205_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4186_, v_positions_4187_, v_params_4188_, v_recFnNames_4189_, v_containsRecFn_4190_, v_ctx_4191_, v_v_4204_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
                    if lean_obj_tag(v___x_4205_) == 0 {
                        v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
                        lean_inc(v_a_4206_);
                        lean_dec_ref_known(v___x_4205_, 1);
                        v___x_4207_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4208_ = lean_array_uset(v_bs_4194_, v_i_4193_, v___x_4207_);
                        v___x_4209_ = 1usize;
                        v___x_4210_ = lean_usize_add(v_i_4193_, v___x_4209_);
                        v___x_4211_ = lean_array_uset(v_bs_x27_4208_, v_i_4193_, v_a_4206_);
                        v_i_4193_ = v___x_4210_;
                        v_bs_4194_ = v___x_4211_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_4194_);
                        lean_dec_ref(v_ctx_4191_);
                        lean_dec_ref(v_containsRecFn_4190_);
                        lean_dec_ref(v_recFnNames_4189_);
                        lean_dec_ref(v_params_4188_);
                        lean_dec_ref(v_positions_4187_);
                        lean_dec_ref(v_recArgInfos_4186_);
                        v_a_4213_ = lean_ctor_get(v___x_4205_, 0);
                        v_isSharedCheck_4220_ = (!lean_is_exclusive(v___x_4205_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v___x_4215_ = v___x_4205_;
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4213_);
                            lean_dec(v___x_4205_);
                            v___x_4215_ = lean_box(0);
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
                    v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
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
    mut v_recArgInfos_4221_: *mut LeanObject,
    mut v_positions_4222_: *mut LeanObject,
    mut v_params_4223_: *mut LeanObject,
    mut v_recFnNames_4224_: *mut LeanObject,
    mut v_containsRecFn_4225_: *mut LeanObject,
    mut v_ctx_4226_: *mut LeanObject,
    mut v_e_4227_: *mut LeanObject,
    mut v_x_4228_: *mut LeanObject,
    mut v_x_4229_: *mut LeanObject,
    mut v_x_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
    mut v___y_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
    mut v___y_4235_: *mut LeanObject,
    mut v___y_4236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fn_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4244_: usize = 0;
    let mut v___x_4245_: usize = 0;
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4259_: u8 = 0;
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4264_: u8 = 0;
    let mut v_declName_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4274_: u8 = 0;
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4228_) == 5 {
                    v_fn_4238_ = lean_ctor_get(v_x_4228_, 0);
                    lean_inc_ref(v_fn_4238_);
                    v_arg_4239_ = lean_ctor_get(v_x_4228_, 1);
                    lean_inc_ref(v_arg_4239_);
                    lean_dec_ref_known(v_x_4228_, 2);
                    v___x_4240_ = lean_array_set(v_x_4229_, v_x_4230_, v_arg_4239_);
                    v___x_4241_ = lean_unsigned_to_nat(1);
                    v___x_4242_ = lean_nat_sub(v_x_4230_, v___x_4241_);
                    lean_dec(v_x_4230_);
                    v_x_4228_ = v_fn_4238_;
                    v_x_4229_ = v___x_4240_;
                    v_x_4230_ = v___x_4242_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_x_4230_);
                    v_sz_4244_ = lean_array_size(v_x_4229_);
                    v___x_4245_ = 0usize;
                    lean_inc_ref(v_ctx_4226_);
                    lean_inc_ref(v_containsRecFn_4225_);
                    lean_inc_ref(v_recFnNames_4224_);
                    lean_inc_ref(v_params_4223_);
                    lean_inc_ref(v_positions_4222_);
                    lean_inc_ref(v_recArgInfos_4221_);
                    v___x_4246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0(v_recArgInfos_4221_, v_positions_4222_, v_params_4223_, v_recFnNames_4224_, v_containsRecFn_4225_, v_ctx_4226_, v_sz_4244_, v___x_4245_, v_x_4229_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
                    if lean_obj_tag(v___x_4246_) == 0 {
                        v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
                        lean_inc(v_a_4247_);
                        lean_dec_ref_known(v___x_4246_, 1);
                        if lean_obj_tag(v_x_4228_) == 4 {
                            v_declName_4265_ = lean_ctor_get(v_x_4228_, 0);
                            v___x_4266_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__1(v_recFnNames_4224_, v_declName_4265_);
                            if lean_obj_tag(v___x_4266_) == 1 {
                                lean_dec_ref_known(v_x_4228_, 2);
                                lean_dec_ref(v_containsRecFn_4225_);
                                lean_dec_ref(v_recFnNames_4224_);
                                lean_dec_ref(v_params_4223_);
                                v_val_4267_ = lean_ctor_get(v___x_4266_, 0);
                                lean_inc(v_val_4267_);
                                lean_dec_ref_known(v___x_4266_, 1);
                                v___x_4268_ =
                                    l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
                                v___x_4269_ =
                                    lean_array_get(v___x_4268_, v_recArgInfos_4221_, v_val_4267_);
                                lean_dec_ref(v_recArgInfos_4221_);
                                v___x_4270_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp(v___x_4269_, v_ctx_4226_, v_val_4267_, v_positions_4222_, v_e_4227_, v_a_4247_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
                                lean_dec(v_a_4247_);
                                lean_dec_ref(v_positions_4222_);
                                lean_dec(v_val_4267_);
                                lean_dec_ref(v_ctx_4226_);
                                lean_dec(v___x_4269_);
                                return v___x_4270_;
                            } else {
                                lean_dec(v___x_4266_);
                                lean_dec_ref(v_e_4227_);
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
                            lean_dec_ref(v_e_4227_);
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
                        lean_dec_ref(v_x_4228_);
                        lean_dec_ref(v_e_4227_);
                        lean_dec_ref(v_ctx_4226_);
                        lean_dec_ref(v_containsRecFn_4225_);
                        lean_dec_ref(v_recFnNames_4224_);
                        lean_dec_ref(v_params_4223_);
                        lean_dec_ref(v_positions_4222_);
                        lean_dec_ref(v_recArgInfos_4221_);
                        v_a_4271_ = lean_ctor_get(v___x_4246_, 0);
                        v_isSharedCheck_4278_ = (!lean_is_exclusive(v___x_4246_)) as u8;
                        if v_isSharedCheck_4278_ == 0 {
                            v___x_4273_ = v___x_4246_;
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4271_);
                            lean_dec(v___x_4246_);
                            v___x_4273_ = lean_box(0);
                            v_isShared_4274_ = v_isSharedCheck_4278_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_4253_);
                v___x_4255_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4221_, v_positions_4222_, v_params_4223_, v_recFnNames_4224_, v_containsRecFn_4225_, v_ctx_4226_, v_x_4228_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_, v___y_4253_, v___y_4254_);
                if lean_obj_tag(v___x_4255_) == 0 {
                    v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
                    v_isSharedCheck_4264_ = (!lean_is_exclusive(v___x_4255_)) as u8;
                    if v_isSharedCheck_4264_ == 0 {
                        v___x_4258_ = v___x_4255_;
                        v_isShared_4259_ = v_isSharedCheck_4264_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4256_);
                        lean_dec(v___x_4255_);
                        v___x_4258_ = lean_box(0);
                        v_isShared_4259_ = v_isSharedCheck_4264_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4247_);
                    return v___x_4255_;
                }
            }
            2 => {
                v___x_4260_ = l_Lean_mkAppN(v_a_4256_, v_a_4247_);
                lean_dec(v_a_4247_);
                if v_isShared_4259_ == 0 {
                    lean_ctor_set(v___x_4258_, 0, v___x_4260_);
                    v___x_4262_ = v___x_4258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4263_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4263_, 0, v___x_4260_);
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
                    v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
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
    mut v_body_4279_: *mut LeanObject,
    mut v_recArgInfos_4280_: *mut LeanObject,
    mut v_positions_4281_: *mut LeanObject,
    mut v_params_4282_: *mut LeanObject,
    mut v_recFnNames_4283_: *mut LeanObject,
    mut v_containsRecFn_4284_: *mut LeanObject,
    mut v_ctx_4285_: *mut LeanObject,
    mut v_a_4286_: u8,
    mut v_x_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
    mut v___y_4292_: *mut LeanObject,
    mut v___y_4293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    v___x_4295_ = lean_expr_instantiate1(v_body_4279_, v_x_4287_);
    lean_inc_ref(v___y_4292_);
    v___x_4296_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4280_, v_positions_4281_, v_params_4282_, v_recFnNames_4283_, v_containsRecFn_4284_, v_ctx_4285_, v___x_4295_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
    if lean_obj_tag(v___x_4296_) == 0 {
        let mut v_a_4297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: u8 = 0;
        let mut v___x_4302_: u8 = 0;
        let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
        v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
        lean_inc(v_a_4297_);
        lean_dec_ref_known(v___x_4296_, 1);
        v___x_4298_ = lean_unsigned_to_nat(1);
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
        lean_dec_ref(v___x_4300_);
        return v___x_4303_;
    } else {
        lean_dec_ref(v_x_4287_);
        return v___x_4296_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__0___boxed(
    mut v_body_4304_: *mut LeanObject,
    mut v_recArgInfos_4305_: *mut LeanObject,
    mut v_positions_4306_: *mut LeanObject,
    mut v_params_4307_: *mut LeanObject,
    mut v_recFnNames_4308_: *mut LeanObject,
    mut v_containsRecFn_4309_: *mut LeanObject,
    mut v_ctx_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_x_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
    mut v___y_4314_: *mut LeanObject,
    mut v___y_4315_: *mut LeanObject,
    mut v___y_4316_: *mut LeanObject,
    mut v___y_4317_: *mut LeanObject,
    mut v___y_4318_: *mut LeanObject,
    mut v___y_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_34753__boxed_4320_: u8 = 0;
    let mut v_res_4321_: *mut LeanObject = core::ptr::null_mut();
    v_a_34753__boxed_4320_ = (lean_unbox(v_a_4311_) as u8);
    v_res_4321_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__0(v_body_4304_, v_recArgInfos_4305_, v_positions_4306_, v_params_4307_, v_recFnNames_4308_, v_containsRecFn_4309_, v_ctx_4310_, v_a_34753__boxed_4320_, v_x_4312_, v___y_4313_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
    lean_dec(v___y_4318_);
    lean_dec_ref(v___y_4317_);
    lean_dec(v___y_4316_);
    lean_dec_ref(v___y_4315_);
    lean_dec(v___y_4314_);
    lean_dec(v___y_4313_);
    lean_dec_ref(v_body_4304_);
    return v_res_4321_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1(
    mut v_body_4322_: *mut LeanObject,
    mut v_recArgInfos_4323_: *mut LeanObject,
    mut v_positions_4324_: *mut LeanObject,
    mut v_params_4325_: *mut LeanObject,
    mut v_recFnNames_4326_: *mut LeanObject,
    mut v_containsRecFn_4327_: *mut LeanObject,
    mut v_ctx_4328_: *mut LeanObject,
    mut v_a_4329_: u8,
    mut v_x_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    v___x_4338_ = lean_expr_instantiate1(v_body_4322_, v_x_4330_);
    lean_inc_ref(v___y_4335_);
    v___x_4339_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4323_, v_positions_4324_, v_params_4325_, v_recFnNames_4326_, v_containsRecFn_4327_, v_ctx_4328_, v___x_4338_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
    if lean_obj_tag(v___x_4339_) == 0 {
        let mut v_a_4340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4344_: u8 = 0;
        let mut v___x_4345_: u8 = 0;
        let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
        v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
        lean_inc(v_a_4340_);
        lean_dec_ref_known(v___x_4339_, 1);
        v___x_4341_ = lean_unsigned_to_nat(1);
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
        lean_dec_ref(v___x_4343_);
        return v___x_4346_;
    } else {
        lean_dec_ref(v_x_4330_);
        return v___x_4339_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1___boxed(
    mut v_body_4347_: *mut LeanObject,
    mut v_recArgInfos_4348_: *mut LeanObject,
    mut v_positions_4349_: *mut LeanObject,
    mut v_params_4350_: *mut LeanObject,
    mut v_recFnNames_4351_: *mut LeanObject,
    mut v_containsRecFn_4352_: *mut LeanObject,
    mut v_ctx_4353_: *mut LeanObject,
    mut v_a_4354_: *mut LeanObject,
    mut v_x_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
    mut v___y_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_34772__boxed_4363_: u8 = 0;
    let mut v_res_4364_: *mut LeanObject = core::ptr::null_mut();
    v_a_34772__boxed_4363_ = (lean_unbox(v_a_4354_) as u8);
    v_res_4364_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1(v_body_4347_, v_recArgInfos_4348_, v_positions_4349_, v_params_4350_, v_recFnNames_4351_, v_containsRecFn_4352_, v_ctx_4353_, v_a_34772__boxed_4363_, v_x_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
    lean_dec(v___y_4361_);
    lean_dec_ref(v___y_4360_);
    lean_dec(v___y_4359_);
    lean_dec_ref(v___y_4358_);
    lean_dec(v___y_4357_);
    lean_dec(v___y_4356_);
    lean_dec_ref(v_body_4347_);
    return v_res_4364_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2(
    mut v_body_4365_: *mut LeanObject,
    mut v_recArgInfos_4366_: *mut LeanObject,
    mut v_positions_4367_: *mut LeanObject,
    mut v_params_4368_: *mut LeanObject,
    mut v_recFnNames_4369_: *mut LeanObject,
    mut v_containsRecFn_4370_: *mut LeanObject,
    mut v_ctx_4371_: *mut LeanObject,
    mut v_x_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
    mut v___y_4378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    v___x_4380_ = lean_expr_instantiate1(v_body_4365_, v_x_4372_);
    lean_inc_ref(v___y_4377_);
    v___x_4381_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4366_, v_positions_4367_, v_params_4368_, v_recFnNames_4369_, v_containsRecFn_4370_, v_ctx_4371_, v___x_4380_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
    return v___x_4381_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2___boxed(
    mut v_body_4382_: *mut LeanObject,
    mut v_recArgInfos_4383_: *mut LeanObject,
    mut v_positions_4384_: *mut LeanObject,
    mut v_params_4385_: *mut LeanObject,
    mut v_recFnNames_4386_: *mut LeanObject,
    mut v_containsRecFn_4387_: *mut LeanObject,
    mut v_ctx_4388_: *mut LeanObject,
    mut v_x_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4397_: *mut LeanObject = core::ptr::null_mut();
    v_res_4397_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2(v_body_4382_, v_recArgInfos_4383_, v_positions_4384_, v_params_4385_, v_recFnNames_4386_, v_containsRecFn_4387_, v_ctx_4388_, v_x_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
    lean_dec(v___y_4395_);
    lean_dec_ref(v___y_4394_);
    lean_dec(v___y_4393_);
    lean_dec_ref(v___y_4392_);
    lean_dec(v___y_4391_);
    lean_dec(v___y_4390_);
    lean_dec_ref(v_x_4389_);
    lean_dec_ref(v_body_4382_);
    return v_res_4397_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__3___boxed(
    mut v_recArgInfos_4398_: *mut LeanObject,
    mut v_positions_4399_: *mut LeanObject,
    mut v_params_4400_: *mut LeanObject,
    mut v_recFnNames_4401_: *mut LeanObject,
    mut v_containsRecFn_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v_ctx_4405_: *mut LeanObject,
    mut v_e_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4412_: *mut LeanObject = core::ptr::null_mut();
    v_res_4412_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__3(v_recArgInfos_4398_, v_positions_4399_, v_params_4400_, v_recFnNames_4401_, v_containsRecFn_4402_, v___y_4403_, v___y_4404_, v_ctx_4405_, v_e_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
    lean_dec(v___y_4410_);
    lean_dec_ref(v___y_4409_);
    lean_dec(v___y_4408_);
    lean_dec_ref(v___y_4407_);
    lean_dec(v___y_4404_);
    lean_dec(v___y_4403_);
    return v_res_4412_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6()
-> *mut LeanObject {
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    v___x_4423_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3;
    v___x_4424_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__5;
    v___x_4425_ = l_Lean_Name_append(v___x_4424_, v___x_4423_);
    return v___x_4425_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8()
-> *mut LeanObject {
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    v___x_4427_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__7;
    v___x_4428_ = l_Lean_stringToMessageData(v___x_4427_);
    return v___x_4428_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(
    mut v_recArgInfos_4429_: *mut LeanObject,
    mut v_positions_4430_: *mut LeanObject,
    mut v_params_4431_: *mut LeanObject,
    mut v_recFnNames_4432_: *mut LeanObject,
    mut v_containsRecFn_4433_: *mut LeanObject,
    mut v_ctx_4434_: *mut LeanObject,
    mut v_e_4435_: *mut LeanObject,
    mut v_a_4436_: *mut LeanObject,
    mut v_a_4437_: *mut LeanObject,
    mut v_a_4438_: *mut LeanObject,
    mut v_a_4439_: *mut LeanObject,
    mut v_a_4440_: *mut LeanObject,
    mut v_a_4441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_e_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: u8 = 0;
    let mut v___x_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4469_: u8 = 0;
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: u8 = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_4478_: u8 = 0;
    let mut v___x_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: u8 = 0;
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_4488_: u8 = 0;
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: u8 = 0;
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4513_: u8 = 0;
    let mut v_cancelTk_x3f_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4515_: u8 = 0;
    let mut v_inheritedTraceOptions_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4525_: usize = 0;
    let mut v___x_4526_: usize = 0;
    let mut v___x_4527_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut v_typeName_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v___x_4544_: usize = 0;
    let mut v___x_4545_: usize = 0;
    let mut v___x_4546_: u8 = 0;
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4554_: u8 = 0;
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4584_: u8 = 0;
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4588_: u8 = 0;
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: u8 = 0;
    let mut v___x_4591_: usize = 0;
    let mut v___x_4592_: usize = 0;
    let mut v___x_4593_: u8 = 0;
    let mut v_options_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4595_: u8 = 0;
    let mut v_inheritedTraceOptions_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4608_: u8 = 0;
    let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4612_: u8 = 0;
    let mut v_a_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4616_: u8 = 0;
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4620_: u8 = 0;
    let mut v___x_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v___x_4626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4628_: u8 = 0;
    let mut v_unused_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4633_: u8 = 0;
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4637_: u8 = 0;
    let mut v_isSharedCheck_4638_: u8 = 0;
    let mut v_a_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4642_: u8 = 0;
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_containsRecFn_4433_);
                lean_inc(v_a_4441_);
                lean_inc_ref(v_a_4440_);
                lean_inc(v_a_4439_);
                lean_inc_ref(v_a_4438_);
                lean_inc(v_a_4437_);
                lean_inc(v_a_4436_);
                lean_inc_ref(v_e_4435_);
                v___x_4457_ = lean_apply_8(
                    v_containsRecFn_4433_,
                    v_e_4435_,
                    v_a_4436_,
                    v_a_4437_,
                    v_a_4438_,
                    v_a_4439_,
                    v_a_4440_,
                    v_a_4441_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4457_) == 0 {
                    v_a_4458_ = lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4638_ = (!lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4638_ == 0 {
                        v___x_4460_ = v___x_4457_;
                        v_isShared_4461_ = v_isSharedCheck_4638_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4458_);
                        lean_dec(v___x_4457_);
                        v___x_4460_ = lean_box(0);
                        v_isShared_4461_ = v_isSharedCheck_4638_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4440_);
                    lean_dec_ref(v_e_4435_);
                    lean_dec_ref(v_ctx_4434_);
                    lean_dec_ref(v_containsRecFn_4433_);
                    lean_dec_ref(v_recFnNames_4432_);
                    lean_dec_ref(v_params_4431_);
                    lean_dec_ref(v_positions_4430_);
                    lean_dec_ref(v_recArgInfos_4429_);
                    v_a_4639_ = lean_ctor_get(v___x_4457_, 0);
                    v_isSharedCheck_4646_ = (!lean_is_exclusive(v___x_4457_)) as u8;
                    if v_isSharedCheck_4646_ == 0 {
                        v___x_4641_ = v___x_4457_;
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_4639_);
                        lean_dec(v___x_4457_);
                        v___x_4641_ = lean_box(0);
                        v_isShared_4642_ = v_isSharedCheck_4646_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v_dummy_4451_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__6);
                v_nargs_4452_ = l_Lean_Expr_getAppNumArgs(v_e_4444_);
                lean_inc(v_nargs_4452_);
                v___x_4453_ = lean_mk_array(v_nargs_4452_, v_dummy_4451_);
                v___x_4454_ = lean_unsigned_to_nat(1);
                v___x_4455_ = lean_nat_sub(v_nargs_4452_, v___x_4454_);
                lean_dec(v_nargs_4452_);
                lean_inc_ref(v_e_4444_);
                v___x_4456_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__2(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_e_4444_, v_e_4444_, v___x_4453_, v___x_4455_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
                lean_dec_ref(v___y_4449_);
                return v___x_4456_;
            }
            2 => {
                v___x_4462_ = (lean_unbox(v_a_4458_) as u8);
                if v___x_4462_ == 0 {
                    lean_dec(v_a_4458_);
                    lean_dec_ref(v_a_4440_);
                    lean_dec_ref(v_ctx_4434_);
                    lean_dec_ref(v_containsRecFn_4433_);
                    lean_dec_ref(v_recFnNames_4432_);
                    lean_dec_ref(v_params_4431_);
                    lean_dec_ref(v_positions_4430_);
                    lean_dec_ref(v_recArgInfos_4429_);
                    if v_isShared_4461_ == 0 {
                        lean_ctor_set(v___x_4460_, 0, v_e_4435_);
                        v___x_4464_ = v___x_4460_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_e_4435_);
                        v___x_4464_ = v_reuseFailAlloc_4465_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4460_);
                    match lean_obj_tag(v_e_4435_) {
                        6 => {
                            v_binderName_4466_ = lean_ctor_get(v_e_4435_, 0);
                            lean_inc(v_binderName_4466_);
                            v_binderType_4467_ = lean_ctor_get(v_e_4435_, 1);
                            lean_inc_ref(v_binderType_4467_);
                            v_body_4468_ = lean_ctor_get(v_e_4435_, 2);
                            lean_inc_ref(v_body_4468_);
                            v_binderInfo_4469_ = lean_ctor_get_uint8(
                                v_e_4435_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_dec_ref_known(v_e_4435_, 3);
                            lean_inc_ref(v_a_4440_);
                            lean_inc_ref(v_ctx_4434_);
                            lean_inc_ref(v_containsRecFn_4433_);
                            lean_inc_ref(v_recFnNames_4432_);
                            lean_inc_ref(v_params_4431_);
                            lean_inc_ref(v_positions_4430_);
                            lean_inc_ref(v_recArgInfos_4429_);
                            v___x_4470_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_binderType_4467_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if lean_obj_tag(v___x_4470_) == 0 {
                                v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
                                lean_inc(v_a_4471_);
                                lean_dec_ref_known(v___x_4470_, 1);
                                v___f_4472_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__0___boxed as *mut core::ffi::c_void, 16, 8);
                                lean_closure_set(v___f_4472_, 0, v_body_4468_);
                                lean_closure_set(v___f_4472_, 1, v_recArgInfos_4429_);
                                lean_closure_set(v___f_4472_, 2, v_positions_4430_);
                                lean_closure_set(v___f_4472_, 3, v_params_4431_);
                                lean_closure_set(v___f_4472_, 4, v_recFnNames_4432_);
                                lean_closure_set(v___f_4472_, 5, v_containsRecFn_4433_);
                                lean_closure_set(v___f_4472_, 6, v_ctx_4434_);
                                lean_closure_set(v___f_4472_, 7, v_a_4458_);
                                v___x_4473_ = 0;
                                v___x_4474_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_binderName_4466_, v_binderInfo_4469_, v_a_4471_, v___f_4472_, v___x_4473_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                lean_dec_ref(v_a_4440_);
                                return v___x_4474_;
                            } else {
                                lean_dec_ref(v_body_4468_);
                                lean_dec(v_binderName_4466_);
                                lean_dec(v_a_4458_);
                                lean_dec_ref(v_a_4440_);
                                lean_dec_ref(v_ctx_4434_);
                                lean_dec_ref(v_containsRecFn_4433_);
                                lean_dec_ref(v_recFnNames_4432_);
                                lean_dec_ref(v_params_4431_);
                                lean_dec_ref(v_positions_4430_);
                                lean_dec_ref(v_recArgInfos_4429_);
                                return v___x_4470_;
                            }
                        }
                        7 => {
                            v_binderName_4475_ = lean_ctor_get(v_e_4435_, 0);
                            lean_inc(v_binderName_4475_);
                            v_binderType_4476_ = lean_ctor_get(v_e_4435_, 1);
                            lean_inc_ref(v_binderType_4476_);
                            v_body_4477_ = lean_ctor_get(v_e_4435_, 2);
                            lean_inc_ref(v_body_4477_);
                            v_binderInfo_4478_ = lean_ctor_get_uint8(
                                v_e_4435_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_dec_ref_known(v_e_4435_, 3);
                            lean_inc_ref(v_a_4440_);
                            lean_inc_ref(v_ctx_4434_);
                            lean_inc_ref(v_containsRecFn_4433_);
                            lean_inc_ref(v_recFnNames_4432_);
                            lean_inc_ref(v_params_4431_);
                            lean_inc_ref(v_positions_4430_);
                            lean_inc_ref(v_recArgInfos_4429_);
                            v___x_4479_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_binderType_4476_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if lean_obj_tag(v___x_4479_) == 0 {
                                v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
                                lean_inc(v_a_4480_);
                                lean_dec_ref_known(v___x_4479_, 1);
                                v___f_4481_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__1___boxed as *mut core::ffi::c_void, 16, 8);
                                lean_closure_set(v___f_4481_, 0, v_body_4477_);
                                lean_closure_set(v___f_4481_, 1, v_recArgInfos_4429_);
                                lean_closure_set(v___f_4481_, 2, v_positions_4430_);
                                lean_closure_set(v___f_4481_, 3, v_params_4431_);
                                lean_closure_set(v___f_4481_, 4, v_recFnNames_4432_);
                                lean_closure_set(v___f_4481_, 5, v_containsRecFn_4433_);
                                lean_closure_set(v___f_4481_, 6, v_ctx_4434_);
                                lean_closure_set(v___f_4481_, 7, v_a_4458_);
                                v___x_4482_ = 0;
                                v___x_4483_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__3___redArg(v_binderName_4475_, v_binderInfo_4478_, v_a_4480_, v___f_4481_, v___x_4482_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                lean_dec_ref(v_a_4440_);
                                return v___x_4483_;
                            } else {
                                lean_dec_ref(v_body_4477_);
                                lean_dec(v_binderName_4475_);
                                lean_dec(v_a_4458_);
                                lean_dec_ref(v_a_4440_);
                                lean_dec_ref(v_ctx_4434_);
                                lean_dec_ref(v_containsRecFn_4433_);
                                lean_dec_ref(v_recFnNames_4432_);
                                lean_dec_ref(v_params_4431_);
                                lean_dec_ref(v_positions_4430_);
                                lean_dec_ref(v_recArgInfos_4429_);
                                return v___x_4479_;
                            }
                        }
                        8 => {
                            v_declName_4484_ = lean_ctor_get(v_e_4435_, 0);
                            lean_inc(v_declName_4484_);
                            v_type_4485_ = lean_ctor_get(v_e_4435_, 1);
                            lean_inc_ref(v_type_4485_);
                            v_value_4486_ = lean_ctor_get(v_e_4435_, 2);
                            lean_inc_ref(v_value_4486_);
                            v_body_4487_ = lean_ctor_get(v_e_4435_, 3);
                            lean_inc_ref(v_body_4487_);
                            v_nondep_4488_ = lean_ctor_get_uint8(
                                v_e_4435_,
                                (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                            );
                            lean_dec_ref_known(v_e_4435_, 4);
                            lean_inc_ref(v_a_4440_);
                            lean_inc_ref(v_ctx_4434_);
                            lean_inc_ref(v_containsRecFn_4433_);
                            lean_inc_ref(v_recFnNames_4432_);
                            lean_inc_ref(v_params_4431_);
                            lean_inc_ref(v_positions_4430_);
                            lean_inc_ref(v_recArgInfos_4429_);
                            v___x_4489_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_type_4485_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if lean_obj_tag(v___x_4489_) == 0 {
                                v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
                                lean_inc(v_a_4490_);
                                lean_dec_ref_known(v___x_4489_, 1);
                                lean_inc_ref(v_a_4440_);
                                lean_inc_ref(v_ctx_4434_);
                                lean_inc_ref(v_containsRecFn_4433_);
                                lean_inc_ref(v_recFnNames_4432_);
                                lean_inc_ref(v_params_4431_);
                                lean_inc_ref(v_positions_4430_);
                                lean_inc_ref(v_recArgInfos_4429_);
                                v___x_4491_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_value_4486_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                if lean_obj_tag(v___x_4491_) == 0 {
                                    v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
                                    lean_inc(v_a_4492_);
                                    lean_dec_ref_known(v___x_4491_, 1);
                                    v___f_4493_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__2___boxed as *mut core::ffi::c_void, 15, 7);
                                    lean_closure_set(v___f_4493_, 0, v_body_4487_);
                                    lean_closure_set(v___f_4493_, 1, v_recArgInfos_4429_);
                                    lean_closure_set(v___f_4493_, 2, v_positions_4430_);
                                    lean_closure_set(v___f_4493_, 3, v_params_4431_);
                                    lean_closure_set(v___f_4493_, 4, v_recFnNames_4432_);
                                    lean_closure_set(v___f_4493_, 5, v_containsRecFn_4433_);
                                    lean_closure_set(v___f_4493_, 6, v_ctx_4434_);
                                    v___x_4494_ = 0;
                                    v___x_4495_ = (lean_unbox(v_a_4458_) as u8);
                                    lean_dec(v_a_4458_);
                                    v___x_4496_ = l_Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4(v_declName_4484_, v_a_4490_, v_a_4492_, v___f_4493_, v_nondep_4488_, v___x_4494_, v___x_4495_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                    lean_dec_ref(v_a_4440_);
                                    return v___x_4496_;
                                } else {
                                    lean_dec(v_a_4490_);
                                    lean_dec_ref(v_body_4487_);
                                    lean_dec(v_declName_4484_);
                                    lean_dec(v_a_4458_);
                                    lean_dec_ref(v_a_4440_);
                                    lean_dec_ref(v_ctx_4434_);
                                    lean_dec_ref(v_containsRecFn_4433_);
                                    lean_dec_ref(v_recFnNames_4432_);
                                    lean_dec_ref(v_params_4431_);
                                    lean_dec_ref(v_positions_4430_);
                                    lean_dec_ref(v_recArgInfos_4429_);
                                    return v___x_4491_;
                                }
                            } else {
                                lean_dec_ref(v_body_4487_);
                                lean_dec_ref(v_value_4486_);
                                lean_dec(v_declName_4484_);
                                lean_dec(v_a_4458_);
                                lean_dec_ref(v_a_4440_);
                                lean_dec_ref(v_ctx_4434_);
                                lean_dec_ref(v_containsRecFn_4433_);
                                lean_dec_ref(v_recFnNames_4432_);
                                lean_dec_ref(v_params_4431_);
                                lean_dec_ref(v_positions_4430_);
                                lean_dec_ref(v_recArgInfos_4429_);
                                return v___x_4489_;
                            }
                        }
                        10 => {
                            lean_dec(v_a_4458_);
                            v_data_4497_ = lean_ctor_get(v_e_4435_, 0);
                            v_expr_4498_ = lean_ctor_get(v_e_4435_, 1);
                            v___x_4499_ = l_Lean_getRecAppSyntax_x3f(v_e_4435_);
                            if lean_obj_tag(v___x_4499_) == 1 {
                                lean_inc_ref(v_expr_4498_);
                                lean_dec_ref_known(v_e_4435_, 2);
                                v_val_4500_ = lean_ctor_get(v___x_4499_, 0);
                                lean_inc(v_val_4500_);
                                lean_dec_ref_known(v___x_4499_, 1);
                                v_fileName_4501_ = lean_ctor_get(v_a_4440_, 0);
                                lean_inc_ref(v_fileName_4501_);
                                v_fileMap_4502_ = lean_ctor_get(v_a_4440_, 1);
                                lean_inc_ref(v_fileMap_4502_);
                                v_options_4503_ = lean_ctor_get(v_a_4440_, 2);
                                lean_inc_ref(v_options_4503_);
                                v_currRecDepth_4504_ = lean_ctor_get(v_a_4440_, 3);
                                lean_inc(v_currRecDepth_4504_);
                                v_maxRecDepth_4505_ = lean_ctor_get(v_a_4440_, 4);
                                lean_inc(v_maxRecDepth_4505_);
                                v_ref_4506_ = lean_ctor_get(v_a_4440_, 5);
                                lean_inc(v_ref_4506_);
                                v_currNamespace_4507_ = lean_ctor_get(v_a_4440_, 6);
                                lean_inc(v_currNamespace_4507_);
                                v_openDecls_4508_ = lean_ctor_get(v_a_4440_, 7);
                                lean_inc(v_openDecls_4508_);
                                v_initHeartbeats_4509_ = lean_ctor_get(v_a_4440_, 8);
                                lean_inc(v_initHeartbeats_4509_);
                                v_maxHeartbeats_4510_ = lean_ctor_get(v_a_4440_, 9);
                                lean_inc(v_maxHeartbeats_4510_);
                                v_quotContext_4511_ = lean_ctor_get(v_a_4440_, 10);
                                lean_inc(v_quotContext_4511_);
                                v_currMacroScope_4512_ = lean_ctor_get(v_a_4440_, 11);
                                lean_inc(v_currMacroScope_4512_);
                                v_diag_4513_ = lean_ctor_get_uint8(
                                    v_a_4440_,
                                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                                );
                                v_cancelTk_x3f_4514_ = lean_ctor_get(v_a_4440_, 12);
                                lean_inc(v_cancelTk_x3f_4514_);
                                v_suppressElabErrors_4515_ = lean_ctor_get_uint8(
                                    v_a_4440_,
                                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                                );
                                v_inheritedTraceOptions_4516_ = lean_ctor_get(v_a_4440_, 13);
                                lean_inc_ref(v_inheritedTraceOptions_4516_);
                                lean_dec_ref(v_a_4440_);
                                v_ref_4517_ = l_Lean_replaceRef(v_val_4500_, v_ref_4506_);
                                lean_dec(v_ref_4506_);
                                lean_dec(v_val_4500_);
                                v___x_4518_ = lean_alloc_ctor(0, 14, (2) as u32);
                                lean_ctor_set(v___x_4518_, 0, v_fileName_4501_);
                                lean_ctor_set(v___x_4518_, 1, v_fileMap_4502_);
                                lean_ctor_set(v___x_4518_, 2, v_options_4503_);
                                lean_ctor_set(v___x_4518_, 3, v_currRecDepth_4504_);
                                lean_ctor_set(v___x_4518_, 4, v_maxRecDepth_4505_);
                                lean_ctor_set(v___x_4518_, 5, v_ref_4517_);
                                lean_ctor_set(v___x_4518_, 6, v_currNamespace_4507_);
                                lean_ctor_set(v___x_4518_, 7, v_openDecls_4508_);
                                lean_ctor_set(v___x_4518_, 8, v_initHeartbeats_4509_);
                                lean_ctor_set(v___x_4518_, 9, v_maxHeartbeats_4510_);
                                lean_ctor_set(v___x_4518_, 10, v_quotContext_4511_);
                                lean_ctor_set(v___x_4518_, 11, v_currMacroScope_4512_);
                                lean_ctor_set(v___x_4518_, 12, v_cancelTk_x3f_4514_);
                                lean_ctor_set(v___x_4518_, 13, v_inheritedTraceOptions_4516_);
                                lean_ctor_set_uint8(
                                    v___x_4518_,
                                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                                    v_diag_4513_,
                                );
                                lean_ctor_set_uint8(
                                    v___x_4518_,
                                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                                    v_suppressElabErrors_4515_,
                                );
                                v_e_4435_ = v_expr_4498_;
                                v_a_4440_ = v___x_4518_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v___x_4499_);
                                lean_inc_ref(v_expr_4498_);
                                v___x_4520_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_expr_4498_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                if lean_obj_tag(v___x_4520_) == 0 {
                                    v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
                                    v_isSharedCheck_4535_ = (!lean_is_exclusive(v___x_4520_)) as u8;
                                    if v_isSharedCheck_4535_ == 0 {
                                        v___x_4523_ = v___x_4520_;
                                        v_isShared_4524_ = v_isSharedCheck_4535_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4521_);
                                        lean_dec(v___x_4520_);
                                        v___x_4523_ = lean_box(0);
                                        v_isShared_4524_ = v_isSharedCheck_4535_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_e_4435_, 2);
                                    return v___x_4520_;
                                }
                            }
                        }
                        11 => {
                            lean_dec(v_a_4458_);
                            v_typeName_4536_ = lean_ctor_get(v_e_4435_, 0);
                            v_idx_4537_ = lean_ctor_get(v_e_4435_, 1);
                            v_struct_4538_ = lean_ctor_get(v_e_4435_, 2);
                            lean_inc_ref(v_struct_4538_);
                            v___x_4539_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4429_, v_positions_4430_, v_params_4431_, v_recFnNames_4432_, v_containsRecFn_4433_, v_ctx_4434_, v_struct_4538_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if lean_obj_tag(v___x_4539_) == 0 {
                                v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
                                v_isSharedCheck_4554_ = (!lean_is_exclusive(v___x_4539_)) as u8;
                                if v_isSharedCheck_4554_ == 0 {
                                    v___x_4542_ = v___x_4539_;
                                    v_isShared_4543_ = v_isSharedCheck_4554_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4540_);
                                    lean_dec(v___x_4539_);
                                    v___x_4542_ = lean_box(0);
                                    v_isShared_4543_ = v_isSharedCheck_4554_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_e_4435_, 3);
                                return v___x_4539_;
                            }
                        }
                        5 => {
                            lean_dec(v_a_4458_);
                            v___x_4555_ = 0;
                            lean_inc_ref(v_e_4435_);
                            v___x_4556_ = l_Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5(v_e_4435_, v___x_4555_, v_a_4436_, v_a_4437_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                            if lean_obj_tag(v___x_4556_) == 0 {
                                v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
                                lean_inc(v_a_4557_);
                                lean_dec_ref_known(v___x_4556_, 1);
                                if lean_obj_tag(v_a_4557_) == 1 {
                                    v_val_4558_ = lean_ctor_get(v_a_4557_, 0);
                                    lean_inc(v_val_4558_);
                                    lean_dec_ref_known(v_a_4557_, 1);
                                    v___x_4559_ = lean_unsigned_to_nat(0);
                                    v___x_4589_ = lean_array_get_size(v_recArgInfos_4429_);
                                    v___x_4590_ = lean_nat_dec_lt(v___x_4559_, v___x_4589_);
                                    if v___x_4590_ == 0 {
                                        lean_dec(v_val_4558_);
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
                                            lean_dec(v_val_4558_);
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
                                                lean_dec(v_val_4558_);
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
                                                v_options_4594_ = lean_ctor_get(v_a_4440_, 2);
                                                v_hasTrace_4595_ = lean_ctor_get_uint8(
                                                    v_options_4594_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 1)
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
                                                        lean_ctor_get(v_a_4440_, 13);
                                                    v___x_4597_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__3;
                                                    v___x_4598_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__6);
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
                                                        v___x_4600_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___closed__8);
                                                        lean_inc(v_val_4558_);
                                                        v___x_4601_ = l_Lean_Meta_MatcherApp_toExpr(
                                                            v_val_4558_,
                                                        );
                                                        v___x_4602_ =
                                                            l_Lean_MessageData_ofExpr(v___x_4601_);
                                                        v___x_4603_ =
                                                            lean_alloc_ctor(7, 2, (0) as u32);
                                                        lean_ctor_set(v___x_4603_, 0, v___x_4600_);
                                                        lean_ctor_set(v___x_4603_, 1, v___x_4602_);
                                                        v___x_4604_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(v___x_4597_, v___x_4603_, v_a_4438_, v_a_4439_, v_a_4440_, v_a_4441_);
                                                        if lean_obj_tag(v___x_4604_) == 0 {
                                                            lean_dec_ref_known(v___x_4604_, 1);
                                                            v___y_4561_ = v_a_4436_;
                                                            v___y_4562_ = v_a_4437_;
                                                            v___y_4563_ = v_a_4438_;
                                                            v___y_4564_ = v_a_4439_;
                                                            v___y_4565_ = v_a_4440_;
                                                            v___y_4566_ = v_a_4441_;
                                                            state = 10;
                                                            continue;
                                                        } else {
                                                            lean_dec(v_val_4558_);
                                                            lean_dec_ref_known(v_e_4435_, 2);
                                                            lean_dec_ref(v_a_4440_);
                                                            lean_dec_ref(v_ctx_4434_);
                                                            lean_dec_ref(v_containsRecFn_4433_);
                                                            lean_dec_ref(v_recFnNames_4432_);
                                                            lean_dec_ref(v_params_4431_);
                                                            lean_dec_ref(v_positions_4430_);
                                                            lean_dec_ref(v_recArgInfos_4429_);
                                                            v_a_4605_ =
                                                                lean_ctor_get(v___x_4604_, 0);
                                                            v_isSharedCheck_4612_ =
                                                                (!lean_is_exclusive(v___x_4604_))
                                                                    as u8;
                                                            if v_isSharedCheck_4612_ == 0 {
                                                                v___x_4607_ = v___x_4604_;
                                                                v_isShared_4608_ =
                                                                    v_isSharedCheck_4612_;
                                                                state = 13;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4605_);
                                                                lean_dec(v___x_4604_);
                                                                v___x_4607_ = lean_box(0);
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
                                    lean_dec(v_a_4557_);
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
                                lean_dec_ref_known(v_e_4435_, 2);
                                lean_dec_ref(v_a_4440_);
                                lean_dec_ref(v_ctx_4434_);
                                lean_dec_ref(v_containsRecFn_4433_);
                                lean_dec_ref(v_recFnNames_4432_);
                                lean_dec_ref(v_params_4431_);
                                lean_dec_ref(v_positions_4430_);
                                lean_dec_ref(v_recArgInfos_4429_);
                                v_a_4613_ = lean_ctor_get(v___x_4556_, 0);
                                v_isSharedCheck_4620_ = (!lean_is_exclusive(v___x_4556_)) as u8;
                                if v_isSharedCheck_4620_ == 0 {
                                    v___x_4615_ = v___x_4556_;
                                    v_isShared_4616_ = v_isSharedCheck_4620_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_4613_);
                                    lean_dec(v___x_4556_);
                                    v___x_4615_ = lean_box(0);
                                    v_isShared_4616_ = v_isSharedCheck_4620_;
                                    state = 15;
                                    continue;
                                }
                            }
                        }
                        _ => {
                            lean_dec(v_a_4458_);
                            lean_dec_ref(v_ctx_4434_);
                            lean_dec_ref(v_containsRecFn_4433_);
                            lean_dec_ref(v_params_4431_);
                            lean_dec_ref(v_positions_4430_);
                            lean_dec_ref(v_recArgInfos_4429_);
                            lean_inc_ref(v_e_4435_);
                            v___x_4621_ = l_Lean_Elab_ensureNoRecFn(
                                v_recFnNames_4432_,
                                v_e_4435_,
                                v_a_4438_,
                                v_a_4439_,
                                v_a_4440_,
                                v_a_4441_,
                            );
                            lean_dec_ref(v_a_4440_);
                            if lean_obj_tag(v___x_4621_) == 0 {
                                v_isSharedCheck_4628_ = (!lean_is_exclusive(v___x_4621_)) as u8;
                                if v_isSharedCheck_4628_ == 0 {
                                    v_unused_4629_ = lean_ctor_get(v___x_4621_, 0);
                                    lean_dec(v_unused_4629_);
                                    v___x_4623_ = v___x_4621_;
                                    v_isShared_4624_ = v_isSharedCheck_4628_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_dec(v___x_4621_);
                                    v___x_4623_ = lean_box(0);
                                    v_isShared_4624_ = v_isSharedCheck_4628_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_e_4435_);
                                v_a_4630_ = lean_ctor_get(v___x_4621_, 0);
                                v_isSharedCheck_4637_ = (!lean_is_exclusive(v___x_4621_)) as u8;
                                if v_isSharedCheck_4637_ == 0 {
                                    v___x_4632_ = v___x_4621_;
                                    v_isShared_4633_ = v_isSharedCheck_4637_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_4630_);
                                    lean_dec(v___x_4621_);
                                    v___x_4632_ = lean_box(0);
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
                    lean_inc(v_data_4497_);
                    lean_dec_ref_known(v_e_4435_, 2);
                    v___x_4528_ = l_Lean_Expr_mdata___override(v_data_4497_, v_a_4521_);
                    if v_isShared_4524_ == 0 {
                        lean_ctor_set(v___x_4523_, 0, v___x_4528_);
                        v___x_4530_ = v___x_4523_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4531_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
                        v___x_4530_ = v_reuseFailAlloc_4531_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4521_);
                    if v_isShared_4524_ == 0 {
                        lean_ctor_set(v___x_4523_, 0, v_e_4435_);
                        v___x_4533_ = v___x_4523_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4534_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_e_4435_);
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
                    lean_inc(v_idx_4537_);
                    lean_inc(v_typeName_4536_);
                    lean_dec_ref_known(v_e_4435_, 3);
                    v___x_4547_ =
                        l_Lean_Expr_proj___override(v_typeName_4536_, v_idx_4537_, v_a_4540_);
                    if v_isShared_4543_ == 0 {
                        lean_ctor_set(v___x_4542_, 0, v___x_4547_);
                        v___x_4549_ = v___x_4542_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4550_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4550_, 0, v___x_4547_);
                        v___x_4549_ = v_reuseFailAlloc_4550_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4540_);
                    if v_isShared_4543_ == 0 {
                        lean_ctor_set(v___x_4542_, 0, v_e_4435_);
                        v___x_4552_ = v___x_4542_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_e_4435_);
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
                v_indGroupInst_4569_ = lean_ctor_get(v___x_4568_, 4);
                v_params_4570_ = lean_ctor_get(v_indGroupInst_4569_, 2);
                lean_inc(v___y_4562_);
                lean_inc(v___y_4561_);
                lean_inc_ref(v_containsRecFn_4433_);
                lean_inc_ref(v_recFnNames_4432_);
                lean_inc_ref_n(v_params_4431_, 2);
                lean_inc_ref(v_positions_4430_);
                lean_inc_ref(v_recArgInfos_4429_);
                v___f_4571_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___lam__3___boxed as *mut core::ffi::c_void, 14, 7);
                lean_closure_set(v___f_4571_, 0, v_recArgInfos_4429_);
                lean_closure_set(v___f_4571_, 1, v_positions_4430_);
                lean_closure_set(v___f_4571_, 2, v_params_4431_);
                lean_closure_set(v___f_4571_, 3, v_recFnNames_4432_);
                lean_closure_set(v___f_4571_, 4, v_containsRecFn_4433_);
                lean_closure_set(v___f_4571_, 5, v___y_4561_);
                lean_closure_set(v___f_4571_, 6, v___y_4562_);
                v___x_4572_ = lean_array_get_size(v_params_4570_);
                lean_inc_ref(v_ctx_4434_);
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
                if lean_obj_tag(v___x_4573_) == 0 {
                    v_a_4574_ = lean_ctor_get(v___x_4573_, 0);
                    lean_inc(v_a_4574_);
                    lean_dec_ref_known(v___x_4573_, 1);
                    if lean_obj_tag(v_a_4574_) == 1 {
                        lean_dec_ref_known(v_e_4435_, 2);
                        v_val_4575_ = lean_ctor_get(v_a_4574_, 0);
                        lean_inc(v_val_4575_);
                        lean_dec_ref_known(v_a_4574_, 1);
                        v_fst_4576_ = lean_ctor_get(v_val_4575_, 0);
                        lean_inc(v_fst_4576_);
                        v_snd_4577_ = lean_ctor_get(v_val_4575_, 1);
                        lean_inc(v_snd_4577_);
                        lean_dec(v_val_4575_);
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
                        lean_dec(v_a_4574_);
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
                    lean_dec_ref(v___y_4565_);
                    lean_dec_ref_known(v_e_4435_, 2);
                    lean_dec_ref(v_ctx_4434_);
                    lean_dec_ref(v_containsRecFn_4433_);
                    lean_dec_ref(v_recFnNames_4432_);
                    lean_dec_ref(v_params_4431_);
                    lean_dec_ref(v_positions_4430_);
                    lean_dec_ref(v_recArgInfos_4429_);
                    v_a_4581_ = lean_ctor_get(v___x_4573_, 0);
                    v_isSharedCheck_4588_ = (!lean_is_exclusive(v___x_4573_)) as u8;
                    if v_isSharedCheck_4588_ == 0 {
                        v___x_4583_ = v___x_4573_;
                        v_isShared_4584_ = v_isSharedCheck_4588_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4581_);
                        lean_dec(v___x_4573_);
                        v___x_4583_ = lean_box(0);
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
                    v_reuseFailAlloc_4587_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4587_, 0, v_a_4581_);
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
                    v_reuseFailAlloc_4611_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
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
                    v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
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
                    lean_ctor_set(v___x_4623_, 0, v_e_4435_);
                    v___x_4626_ = v___x_4623_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_e_4435_);
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
                    v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
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
                    v_reuseFailAlloc_4645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4645_, 0, v_a_4639_);
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
    mut v_recArgInfos_4647_: *mut LeanObject,
    mut v_positions_4648_: *mut LeanObject,
    mut v_params_4649_: *mut LeanObject,
    mut v_recFnNames_4650_: *mut LeanObject,
    mut v_containsRecFn_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v_ctx_4654_: *mut LeanObject,
    mut v_e_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
    mut v___y_4658_: *mut LeanObject,
    mut v___y_4659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v___y_4658_);
    v___x_4661_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4647_, v_positions_4648_, v_params_4649_, v_recFnNames_4650_, v_containsRecFn_4651_, v_ctx_4654_, v_e_4655_, v___y_4652_, v___y_4653_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
    return v___x_4661_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0___boxed(
    mut v_recArgInfos_4662_: *mut LeanObject,
    mut v_positions_4663_: *mut LeanObject,
    mut v_params_4664_: *mut LeanObject,
    mut v_recFnNames_4665_: *mut LeanObject,
    mut v_containsRecFn_4666_: *mut LeanObject,
    mut v_ctx_4667_: *mut LeanObject,
    mut v_sz_4668_: *mut LeanObject,
    mut v_i_4669_: *mut LeanObject,
    mut v_bs_4670_: *mut LeanObject,
    mut v___y_4671_: *mut LeanObject,
    mut v___y_4672_: *mut LeanObject,
    mut v___y_4673_: *mut LeanObject,
    mut v___y_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
    mut v___y_4676_: *mut LeanObject,
    mut v___y_4677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4678_: usize = 0;
    let mut v_i_boxed_4679_: usize = 0;
    let mut v_res_4680_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4678_ = lean_unbox_usize(v_sz_4668_);
    lean_dec(v_sz_4668_);
    v_i_boxed_4679_ = lean_unbox_usize(v_i_4669_);
    lean_dec(v_i_4669_);
    v_res_4680_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__0(v_recArgInfos_4662_, v_positions_4663_, v_params_4664_, v_recFnNames_4665_, v_containsRecFn_4666_, v_ctx_4667_, v_sz_boxed_4678_, v_i_boxed_4679_, v_bs_4670_, v___y_4671_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_);
    lean_dec(v___y_4676_);
    lean_dec_ref(v___y_4675_);
    lean_dec(v___y_4674_);
    lean_dec_ref(v___y_4673_);
    lean_dec(v___y_4672_);
    lean_dec(v___y_4671_);
    return v_res_4680_;
}
pub unsafe fn l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_recArgInfos_4681_: *mut LeanObject = *_args.add(0);
    let mut v_positions_4682_: *mut LeanObject = *_args.add(1);
    let mut v_params_4683_: *mut LeanObject = *_args.add(2);
    let mut v_recFnNames_4684_: *mut LeanObject = *_args.add(3);
    let mut v_containsRecFn_4685_: *mut LeanObject = *_args.add(4);
    let mut v_ctx_4686_: *mut LeanObject = *_args.add(5);
    let mut v_e_4687_: *mut LeanObject = *_args.add(6);
    let mut v_x_4688_: *mut LeanObject = *_args.add(7);
    let mut v_x_4689_: *mut LeanObject = *_args.add(8);
    let mut v_x_4690_: *mut LeanObject = *_args.add(9);
    let mut v___y_4691_: *mut LeanObject = *_args.add(10);
    let mut v___y_4692_: *mut LeanObject = *_args.add(11);
    let mut v___y_4693_: *mut LeanObject = *_args.add(12);
    let mut v___y_4694_: *mut LeanObject = *_args.add(13);
    let mut v___y_4695_: *mut LeanObject = *_args.add(14);
    let mut v___y_4696_: *mut LeanObject = *_args.add(15);
    let mut v___y_4697_: *mut LeanObject = *_args.add(16);
    let mut v_res_4698_: *mut LeanObject = core::ptr::null_mut();
    v_res_4698_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__2(v_recArgInfos_4681_, v_positions_4682_, v_params_4683_, v_recFnNames_4684_, v_containsRecFn_4685_, v_ctx_4686_, v_e_4687_, v_x_4688_, v_x_4689_, v_x_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
    lean_dec(v___y_4696_);
    lean_dec_ref(v___y_4695_);
    lean_dec(v___y_4694_);
    lean_dec_ref(v___y_4693_);
    lean_dec(v___y_4692_);
    lean_dec(v___y_4691_);
    return v_res_4698_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop___boxed(
    mut v_recArgInfos_4699_: *mut LeanObject,
    mut v_positions_4700_: *mut LeanObject,
    mut v_params_4701_: *mut LeanObject,
    mut v_recFnNames_4702_: *mut LeanObject,
    mut v_containsRecFn_4703_: *mut LeanObject,
    mut v_ctx_4704_: *mut LeanObject,
    mut v_e_4705_: *mut LeanObject,
    mut v_a_4706_: *mut LeanObject,
    mut v_a_4707_: *mut LeanObject,
    mut v_a_4708_: *mut LeanObject,
    mut v_a_4709_: *mut LeanObject,
    mut v_a_4710_: *mut LeanObject,
    mut v_a_4711_: *mut LeanObject,
    mut v_a_4712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4713_: *mut LeanObject = core::ptr::null_mut();
    v_res_4713_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4699_, v_positions_4700_, v_params_4701_, v_recFnNames_4702_, v_containsRecFn_4703_, v_ctx_4704_, v_e_4705_, v_a_4706_, v_a_4707_, v_a_4708_, v_a_4709_, v_a_4710_, v_a_4711_);
    lean_dec(v_a_4711_);
    lean_dec(v_a_4709_);
    lean_dec_ref(v_a_4708_);
    lean_dec(v_a_4707_);
    lean_dec(v_a_4706_);
    return v_res_4713_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5(
    mut v_00_u03b1_4714_: *mut LeanObject,
    mut v_name_4715_: *mut LeanObject,
    mut v_type_4716_: *mut LeanObject,
    mut v_val_4717_: *mut LeanObject,
    mut v_k_4718_: *mut LeanObject,
    mut v_nondep_4719_: u8,
    mut v_kind_4720_: u8,
    mut v___y_4721_: *mut LeanObject,
    mut v___y_4722_: *mut LeanObject,
    mut v___y_4723_: *mut LeanObject,
    mut v___y_4724_: *mut LeanObject,
    mut v___y_4725_: *mut LeanObject,
    mut v___y_4726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    v___x_4728_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___redArg(v_name_4715_, v_type_4716_, v_val_4717_, v_k_4718_, v_nondep_4719_, v_kind_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
    return v___x_4728_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5___boxed(
    mut v_00_u03b1_4729_: *mut LeanObject,
    mut v_name_4730_: *mut LeanObject,
    mut v_type_4731_: *mut LeanObject,
    mut v_val_4732_: *mut LeanObject,
    mut v_k_4733_: *mut LeanObject,
    mut v_nondep_4734_: *mut LeanObject,
    mut v_kind_4735_: *mut LeanObject,
    mut v___y_4736_: *mut LeanObject,
    mut v___y_4737_: *mut LeanObject,
    mut v___y_4738_: *mut LeanObject,
    mut v___y_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
    mut v___y_4742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_4743_: u8 = 0;
    let mut v_kind_boxed_4744_: u8 = 0;
    let mut v_res_4745_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_4743_ = (lean_unbox(v_nondep_4734_) as u8);
    v_kind_boxed_4744_ = (lean_unbox(v_kind_4735_) as u8);
    v_res_4745_ = l_Lean_Meta_withLetDecl___at___00Lean_Meta_mapLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__4_spec__5(v_00_u03b1_4729_, v_name_4730_, v_type_4731_, v_val_4732_, v_k_4733_, v_nondep_boxed_4743_, v_kind_boxed_4744_, v___y_4736_, v___y_4737_, v___y_4738_, v___y_4739_, v___y_4740_, v___y_4741_);
    lean_dec(v___y_4741_);
    lean_dec_ref(v___y_4740_);
    lean_dec(v___y_4739_);
    lean_dec_ref(v___y_4738_);
    lean_dec(v___y_4737_);
    lean_dec(v___y_4736_);
    return v_res_4745_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9(
    mut v_declName_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
    mut v___y_4751_: *mut LeanObject,
    mut v___y_4752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4754_: *mut LeanObject = core::ptr::null_mut();
    v___x_4754_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___redArg(v_declName_4746_, v___y_4752_);
    return v___x_4754_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9___boxed(
    mut v_declName_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4763_: *mut LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Lean_Meta_getMatcherInfo_x3f___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__9(v_declName_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_);
    lean_dec(v___y_4761_);
    lean_dec_ref(v___y_4760_);
    lean_dec(v___y_4759_);
    lean_dec_ref(v___y_4758_);
    lean_dec(v___y_4757_);
    lean_dec(v___y_4756_);
    return v_res_4763_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7(
    mut v_cls_4764_: *mut LeanObject,
    mut v_msg_4765_: *mut LeanObject,
    mut v___y_4766_: *mut LeanObject,
    mut v___y_4767_: *mut LeanObject,
    mut v___y_4768_: *mut LeanObject,
    mut v___y_4769_: *mut LeanObject,
    mut v___y_4770_: *mut LeanObject,
    mut v___y_4771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    v___x_4773_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___redArg(v_cls_4764_, v_msg_4765_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_);
    return v___x_4773_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7___boxed(
    mut v_cls_4774_: *mut LeanObject,
    mut v_msg_4775_: *mut LeanObject,
    mut v___y_4776_: *mut LeanObject,
    mut v___y_4777_: *mut LeanObject,
    mut v___y_4778_: *mut LeanObject,
    mut v___y_4779_: *mut LeanObject,
    mut v___y_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
    mut v___y_4782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4783_: *mut LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_addTrace___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__7(v_cls_4774_, v_msg_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
    lean_dec(v___y_4781_);
    lean_dec_ref(v___y_4780_);
    lean_dec(v___y_4779_);
    lean_dec_ref(v___y_4778_);
    lean_dec(v___y_4777_);
    lean_dec(v___y_4776_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9(
    mut v_00_u03b1_4784_: *mut LeanObject,
    mut v_constName_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
    mut v___y_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
    mut v___y_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    v___x_4793_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___redArg(v_constName_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
    return v___x_4793_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_4794_: *mut LeanObject,
    mut v_constName_4795_: *mut LeanObject,
    mut v___y_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
    mut v___y_4802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4803_: *mut LeanObject = core::ptr::null_mut();
    v_res_4803_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9(v_00_u03b1_4794_, v_constName_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_);
    lean_dec(v___y_4801_);
    lean_dec_ref(v___y_4800_);
    lean_dec(v___y_4799_);
    lean_dec_ref(v___y_4798_);
    lean_dec(v___y_4797_);
    lean_dec(v___y_4796_);
    return v_res_4803_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14(
    mut v_00_u03b1_4804_: *mut LeanObject,
    mut v_ref_4805_: *mut LeanObject,
    mut v_constName_4806_: *mut LeanObject,
    mut v___y_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
    mut v___y_4810_: *mut LeanObject,
    mut v___y_4811_: *mut LeanObject,
    mut v___y_4812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    v___x_4814_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___redArg(v_ref_4805_, v_constName_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
    return v___x_4814_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14___boxed(
    mut v_00_u03b1_4815_: *mut LeanObject,
    mut v_ref_4816_: *mut LeanObject,
    mut v_constName_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
    mut v___y_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4825_: *mut LeanObject = core::ptr::null_mut();
    v_res_4825_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14(v_00_u03b1_4815_, v_ref_4816_, v_constName_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_);
    lean_dec(v___y_4823_);
    lean_dec_ref(v___y_4822_);
    lean_dec(v___y_4821_);
    lean_dec_ref(v___y_4820_);
    lean_dec(v___y_4819_);
    lean_dec(v___y_4818_);
    lean_dec(v_ref_4816_);
    return v_res_4825_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16(
    mut v_00_u03b1_4826_: *mut LeanObject,
    mut v_ref_4827_: *mut LeanObject,
    mut v_msg_4828_: *mut LeanObject,
    mut v_declHint_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
    mut v___y_4831_: *mut LeanObject,
    mut v___y_4832_: *mut LeanObject,
    mut v___y_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    v___x_4837_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___redArg(v_ref_4827_, v_msg_4828_, v_declHint_4829_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
    return v___x_4837_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16___boxed(
    mut v_00_u03b1_4838_: *mut LeanObject,
    mut v_ref_4839_: *mut LeanObject,
    mut v_msg_4840_: *mut LeanObject,
    mut v_declHint_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
    mut v___y_4843_: *mut LeanObject,
    mut v___y_4844_: *mut LeanObject,
    mut v___y_4845_: *mut LeanObject,
    mut v___y_4846_: *mut LeanObject,
    mut v___y_4847_: *mut LeanObject,
    mut v___y_4848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4849_: *mut LeanObject = core::ptr::null_mut();
    v_res_4849_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16(v_00_u03b1_4838_, v_ref_4839_, v_msg_4840_, v_declHint_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, v___y_4847_);
    lean_dec(v___y_4847_);
    lean_dec_ref(v___y_4846_);
    lean_dec(v___y_4845_);
    lean_dec_ref(v___y_4844_);
    lean_dec(v___y_4843_);
    lean_dec(v___y_4842_);
    lean_dec(v_ref_4839_);
    return v_res_4849_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18(
    mut v_msg_4850_: *mut LeanObject,
    mut v_declHint_4851_: *mut LeanObject,
    mut v___y_4852_: *mut LeanObject,
    mut v___y_4853_: *mut LeanObject,
    mut v___y_4854_: *mut LeanObject,
    mut v___y_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    v___x_4859_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___redArg(v_msg_4850_, v_declHint_4851_, v___y_4857_);
    return v___x_4859_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18___boxed(
    mut v_msg_4860_: *mut LeanObject,
    mut v_declHint_4861_: *mut LeanObject,
    mut v___y_4862_: *mut LeanObject,
    mut v___y_4863_: *mut LeanObject,
    mut v___y_4864_: *mut LeanObject,
    mut v___y_4865_: *mut LeanObject,
    mut v___y_4866_: *mut LeanObject,
    mut v___y_4867_: *mut LeanObject,
    mut v___y_4868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4869_: *mut LeanObject = core::ptr::null_mut();
    v_res_4869_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__17_spec__18(v_msg_4860_, v_declHint_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_, v___y_4866_, v___y_4867_);
    lean_dec(v___y_4867_);
    lean_dec_ref(v___y_4866_);
    lean_dec(v___y_4865_);
    lean_dec_ref(v___y_4864_);
    lean_dec(v___y_4863_);
    lean_dec(v___y_4862_);
    return v_res_4869_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18(
    mut v_00_u03b1_4870_: *mut LeanObject,
    mut v_ref_4871_: *mut LeanObject,
    mut v_msg_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
    mut v___y_4874_: *mut LeanObject,
    mut v___y_4875_: *mut LeanObject,
    mut v___y_4876_: *mut LeanObject,
    mut v___y_4877_: *mut LeanObject,
    mut v___y_4878_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    v___x_4880_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___redArg(v_ref_4871_, v_msg_4872_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_, v___y_4877_, v___y_4878_);
    return v___x_4880_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18___boxed(
    mut v_00_u03b1_4881_: *mut LeanObject,
    mut v_ref_4882_: *mut LeanObject,
    mut v_msg_4883_: *mut LeanObject,
    mut v___y_4884_: *mut LeanObject,
    mut v___y_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4891_: *mut LeanObject = core::ptr::null_mut();
    v_res_4891_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18(v_00_u03b1_4881_, v_ref_4882_, v_msg_4883_, v___y_4884_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_);
    lean_dec(v___y_4889_);
    lean_dec_ref(v___y_4888_);
    lean_dec(v___y_4887_);
    lean_dec_ref(v___y_4886_);
    lean_dec(v___y_4885_);
    lean_dec(v___y_4884_);
    lean_dec(v_ref_4882_);
    return v_res_4891_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20(
    mut v_00_u03b1_4892_: *mut LeanObject,
    mut v_msg_4893_: *mut LeanObject,
    mut v___y_4894_: *mut LeanObject,
    mut v___y_4895_: *mut LeanObject,
    mut v___y_4896_: *mut LeanObject,
    mut v___y_4897_: *mut LeanObject,
    mut v___y_4898_: *mut LeanObject,
    mut v___y_4899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    v___x_4901_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___redArg(v_msg_4893_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
    return v___x_4901_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20___boxed(
    mut v_00_u03b1_4902_: *mut LeanObject,
    mut v_msg_4903_: *mut LeanObject,
    mut v___y_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
    mut v___y_4906_: *mut LeanObject,
    mut v___y_4907_: *mut LeanObject,
    mut v___y_4908_: *mut LeanObject,
    mut v___y_4909_: *mut LeanObject,
    mut v___y_4910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4911_: *mut LeanObject = core::ptr::null_mut();
    v_res_4911_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_matchMatcherApp_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop_spec__5_spec__7_spec__9_spec__14_spec__16_spec__18_spec__20(v_00_u03b1_4902_, v_msg_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_, v___y_4909_);
    lean_dec(v___y_4909_);
    lean_dec_ref(v___y_4908_);
    lean_dec(v___y_4907_);
    lean_dec_ref(v___y_4906_);
    lean_dec(v___y_4905_);
    lean_dec(v___y_4904_);
    return v_res_4911_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0(
    mut v_recFnNames_4912_: *mut LeanObject,
    mut v_e_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
    mut v___y_4915_: *mut LeanObject,
    mut v___y_4916_: *mut LeanObject,
    mut v___y_4917_: *mut LeanObject,
    mut v___y_4918_: *mut LeanObject,
    mut v___y_4919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    v___x_4921_ = lean_st_ref_take(v___y_4914_);
    v___x_4922_ = l_Lean_HasConstCache_containsUnsafe(v_recFnNames_4912_, v_e_4913_, v___x_4921_);
    v_fst_4923_ = lean_ctor_get(v___x_4922_, 0);
    lean_inc(v_fst_4923_);
    v_snd_4924_ = lean_ctor_get(v___x_4922_, 1);
    lean_inc(v_snd_4924_);
    lean_dec_ref(v___x_4922_);
    v___x_4925_ = lean_st_ref_set(v___y_4914_, v_snd_4924_);
    v___x_4926_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4926_, 0, v_fst_4923_);
    return v___x_4926_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0___boxed(
    mut v_recFnNames_4927_: *mut LeanObject,
    mut v_e_4928_: *mut LeanObject,
    mut v___y_4929_: *mut LeanObject,
    mut v___y_4930_: *mut LeanObject,
    mut v___y_4931_: *mut LeanObject,
    mut v___y_4932_: *mut LeanObject,
    mut v___y_4933_: *mut LeanObject,
    mut v___y_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4936_: *mut LeanObject = core::ptr::null_mut();
    v_res_4936_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0(v_recFnNames_4927_, v_e_4928_, v___y_4929_, v___y_4930_, v___y_4931_, v___y_4932_, v___y_4933_, v___y_4934_);
    lean_dec(v___y_4934_);
    lean_dec_ref(v___y_4933_);
    lean_dec(v___y_4932_);
    lean_dec_ref(v___y_4931_);
    lean_dec(v___y_4930_);
    lean_dec(v___y_4929_);
    lean_dec_ref(v_recFnNames_4927_);
    return v_res_4936_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_spec__0(
    mut v_sz_4937_: usize,
    mut v_i_4938_: usize,
    mut v_bs_4939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4940_: u8 = 0;
    let mut v_v_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnName_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: usize = 0;
    let mut v___x_4946_: usize = 0;
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4940_ = lean_usize_dec_lt(v_i_4938_, v_sz_4937_);
                if v___x_4940_ == 0 {
                    return v_bs_4939_;
                } else {
                    v_v_4941_ = lean_array_uget_borrowed(v_bs_4939_, v_i_4938_);
                    v_fnName_4942_ = lean_ctor_get(v_v_4941_, 0);
                    lean_inc(v_fnName_4942_);
                    v___x_4943_ = lean_unsigned_to_nat(0);
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
    mut v_sz_4949_: *mut LeanObject,
    mut v_i_4950_: *mut LeanObject,
    mut v_bs_4951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4952_: usize = 0;
    let mut v_i_boxed_4953_: usize = 0;
    let mut v_res_4954_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4952_ = lean_unbox_usize(v_sz_4949_);
    lean_dec(v_sz_4949_);
    v_i_boxed_4953_ = lean_unbox_usize(v_i_4950_);
    lean_dec(v_i_4950_);
    v_res_4954_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_spec__0(v_sz_boxed_4952_, v_i_boxed_4953_, v_bs_4951_);
    return v_res_4954_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0()
-> *mut LeanObject {
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    v___x_4955_ = lean_box(0);
    v___x_4956_ = lean_unsigned_to_nat(16);
    v___x_4957_ = lean_mk_array(v___x_4956_, v___x_4955_);
    return v___x_4957_;
}
pub unsafe fn _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1()
-> *mut LeanObject {
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    v___x_4958_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__0);
    v___x_4959_ = lean_unsigned_to_nat(0);
    v___x_4960_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4960_, 0, v___x_4959_);
    lean_ctor_set(v___x_4960_, 1, v___x_4958_);
    return v___x_4960_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps(
    mut v_recArgInfos_4961_: *mut LeanObject,
    mut v_positions_4962_: *mut LeanObject,
    mut v_params_4963_: *mut LeanObject,
    mut v_ctx_4964_: *mut LeanObject,
    mut v_e_4965_: *mut LeanObject,
    mut v_a_4966_: *mut LeanObject,
    mut v_a_4967_: *mut LeanObject,
    mut v_a_4968_: *mut LeanObject,
    mut v_a_4969_: *mut LeanObject,
    mut v_a_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4974_: usize = 0;
    let mut v___x_4975_: usize = 0;
    let mut v_recFnNames_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_containsRecFn_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4982_: u8 = 0;
    let mut v___x_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4987_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4972_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1_once), _init_l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___closed__1);
                v___x_4973_ = lean_st_mk_ref(v___x_4972_);
                v_sz_4974_ = lean_array_size(v_recArgInfos_4961_);
                v___x_4975_ = 0usize;
                lean_inc_ref(v_recArgInfos_4961_);
                v_recFnNames_4976_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_spec__0(v_sz_4974_, v___x_4975_, v_recArgInfos_4961_);
                lean_inc_ref(v_recFnNames_4976_);
                v_containsRecFn_4977_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___lam__0___boxed as *mut core::ffi::c_void, 9, 1);
                lean_closure_set(v_containsRecFn_4977_, 0, v_recFnNames_4976_);
                lean_inc_ref(v_a_4969_);
                v___x_4978_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps_loop(v_recArgInfos_4961_, v_positions_4962_, v_params_4963_, v_recFnNames_4976_, v_containsRecFn_4977_, v_ctx_4964_, v_e_4965_, v___x_4973_, v_a_4966_, v_a_4967_, v_a_4968_, v_a_4969_, v_a_4970_);
                if lean_obj_tag(v___x_4978_) == 0 {
                    v_a_4979_ = lean_ctor_get(v___x_4978_, 0);
                    v_isSharedCheck_4987_ = (!lean_is_exclusive(v___x_4978_)) as u8;
                    if v_isSharedCheck_4987_ == 0 {
                        v___x_4981_ = v___x_4978_;
                        v_isShared_4982_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4979_);
                        lean_dec(v___x_4978_);
                        v___x_4981_ = lean_box(0);
                        v_isShared_4982_ = v_isSharedCheck_4987_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4973_);
                    return v___x_4978_;
                }
            }
            1 => {
                v___x_4983_ = lean_st_ref_get(v___x_4973_);
                lean_dec(v___x_4973_);
                lean_dec(v___x_4983_);
                if v_isShared_4982_ == 0 {
                    v___x_4985_ = v___x_4981_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4986_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_a_4979_);
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
    mut v_recArgInfos_4988_: *mut LeanObject,
    mut v_positions_4989_: *mut LeanObject,
    mut v_params_4990_: *mut LeanObject,
    mut v_ctx_4991_: *mut LeanObject,
    mut v_e_4992_: *mut LeanObject,
    mut v_a_4993_: *mut LeanObject,
    mut v_a_4994_: *mut LeanObject,
    mut v_a_4995_: *mut LeanObject,
    mut v_a_4996_: *mut LeanObject,
    mut v_a_4997_: *mut LeanObject,
    mut v_a_4998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4999_: *mut LeanObject = core::ptr::null_mut();
    v_res_4999_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps(v_recArgInfos_4988_, v_positions_4989_, v_params_4990_, v_ctx_4991_, v_e_4992_, v_a_4993_, v_a_4994_, v_a_4995_, v_a_4996_, v_a_4997_);
    lean_dec(v_a_4997_);
    lean_dec_ref(v_a_4996_);
    lean_dec(v_a_4995_);
    lean_dec_ref(v_a_4994_);
    lean_dec(v_a_4993_);
    return v_res_4999_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0(
    mut v_k_5000_: *mut LeanObject,
    mut v_b_5001_: *mut LeanObject,
    mut v___y_5002_: *mut LeanObject,
    mut v___y_5003_: *mut LeanObject,
    mut v___y_5004_: *mut LeanObject,
    mut v___y_5005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5007_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5005_);
    lean_inc_ref(v___y_5004_);
    lean_inc(v___y_5003_);
    lean_inc_ref(v___y_5002_);
    v___x_5007_ = lean_apply_6(
        v_k_5000_,
        v_b_5001_,
        v___y_5002_,
        v___y_5003_,
        v___y_5004_,
        v___y_5005_,
        lean_box(0),
    );
    return v___x_5007_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0___boxed(
    mut v_k_5008_: *mut LeanObject,
    mut v_b_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
    mut v___y_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5015_: *mut LeanObject = core::ptr::null_mut();
    v_res_5015_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0(v_k_5008_, v_b_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_);
    lean_dec(v___y_5013_);
    lean_dec_ref(v___y_5012_);
    lean_dec(v___y_5011_);
    lean_dec_ref(v___y_5010_);
    return v_res_5015_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(
    mut v_name_5016_: *mut LeanObject,
    mut v_type_5017_: *mut LeanObject,
    mut v_val_5018_: *mut LeanObject,
    mut v_k_5019_: *mut LeanObject,
    mut v_nondep_5020_: u8,
    mut v_kind_5021_: u8,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5032_: u8 = 0;
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_a_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5040_: u8 = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5027_ = lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_5027_, 0, v_k_5019_);
                v___x_5028_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_5028_) == 0 {
                    v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
                    v_isSharedCheck_5036_ = (!lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v___x_5031_ = v___x_5028_;
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5029_);
                        lean_dec(v___x_5028_);
                        v___x_5031_ = lean_box(0);
                        v_isShared_5032_ = v_isSharedCheck_5036_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5037_ = lean_ctor_get(v___x_5028_, 0);
                    v_isSharedCheck_5044_ = (!lean_is_exclusive(v___x_5028_)) as u8;
                    if v_isSharedCheck_5044_ == 0 {
                        v___x_5039_ = v___x_5028_;
                        v_isShared_5040_ = v_isSharedCheck_5044_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5037_);
                        lean_dec(v___x_5028_);
                        v___x_5039_ = lean_box(0);
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
                    v_reuseFailAlloc_5035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5035_, 0, v_a_5029_);
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
                    v_reuseFailAlloc_5043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5043_, 0, v_a_5037_);
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
    mut v_name_5045_: *mut LeanObject,
    mut v_type_5046_: *mut LeanObject,
    mut v_val_5047_: *mut LeanObject,
    mut v_k_5048_: *mut LeanObject,
    mut v_nondep_5049_: *mut LeanObject,
    mut v_kind_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
    mut v___y_5052_: *mut LeanObject,
    mut v___y_5053_: *mut LeanObject,
    mut v___y_5054_: *mut LeanObject,
    mut v___y_5055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_5056_: u8 = 0;
    let mut v_kind_boxed_5057_: u8 = 0;
    let mut v_res_5058_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5056_ = (lean_unbox(v_nondep_5049_) as u8);
    v_kind_boxed_5057_ = (lean_unbox(v_kind_5050_) as u8);
    v_res_5058_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(v_name_5045_, v_type_5046_, v_val_5047_, v_k_5048_, v_nondep_boxed_5056_, v_kind_boxed_5057_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
    lean_dec(v___y_5054_);
    lean_dec_ref(v___y_5053_);
    lean_dec(v___y_5052_);
    lean_dec_ref(v___y_5051_);
    return v_res_5058_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0(
    mut v_00_u03b1_5059_: *mut LeanObject,
    mut v_name_5060_: *mut LeanObject,
    mut v_type_5061_: *mut LeanObject,
    mut v_val_5062_: *mut LeanObject,
    mut v_k_5063_: *mut LeanObject,
    mut v_nondep_5064_: u8,
    mut v_kind_5065_: u8,
    mut v___y_5066_: *mut LeanObject,
    mut v___y_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5071_: *mut LeanObject = core::ptr::null_mut();
    v___x_5071_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(v_name_5060_, v_type_5061_, v_val_5062_, v_k_5063_, v_nondep_5064_, v_kind_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
    return v___x_5071_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___boxed(
    mut v_00_u03b1_5072_: *mut LeanObject,
    mut v_name_5073_: *mut LeanObject,
    mut v_type_5074_: *mut LeanObject,
    mut v_val_5075_: *mut LeanObject,
    mut v_k_5076_: *mut LeanObject,
    mut v_nondep_5077_: *mut LeanObject,
    mut v_kind_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
    mut v___y_5081_: *mut LeanObject,
    mut v___y_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_5084_: u8 = 0;
    let mut v_kind_boxed_5085_: u8 = 0;
    let mut v_res_5086_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_5084_ = (lean_unbox(v_nondep_5077_) as u8);
    v_kind_boxed_5085_ = (lean_unbox(v_kind_5078_) as u8);
    v_res_5086_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0(v_00_u03b1_5072_, v_name_5073_, v_type_5074_, v_val_5075_, v_k_5076_, v_nondep_boxed_5084_, v_kind_boxed_5085_, v___y_5079_, v___y_5080_, v___y_5081_, v___y_5082_);
    lean_dec(v___y_5082_);
    lean_dec_ref(v___y_5081_);
    lean_dec(v___y_5080_);
    lean_dec_ref(v___y_5079_);
    return v_res_5086_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0(
    mut v_k_5087_: *mut LeanObject,
    mut v_b_5088_: *mut LeanObject,
    mut v_c_5089_: *mut LeanObject,
    mut v___y_5090_: *mut LeanObject,
    mut v___y_5091_: *mut LeanObject,
    mut v___y_5092_: *mut LeanObject,
    mut v___y_5093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5095_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5093_);
    lean_inc_ref(v___y_5092_);
    lean_inc(v___y_5091_);
    lean_inc_ref(v___y_5090_);
    v___x_5095_ = lean_apply_7(
        v_k_5087_,
        v_b_5088_,
        v_c_5089_,
        v___y_5090_,
        v___y_5091_,
        v___y_5092_,
        v___y_5093_,
        lean_box(0),
    );
    return v___x_5095_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0___boxed(
    mut v_k_5096_: *mut LeanObject,
    mut v_b_5097_: *mut LeanObject,
    mut v_c_5098_: *mut LeanObject,
    mut v___y_5099_: *mut LeanObject,
    mut v___y_5100_: *mut LeanObject,
    mut v___y_5101_: *mut LeanObject,
    mut v___y_5102_: *mut LeanObject,
    mut v___y_5103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5104_: *mut LeanObject = core::ptr::null_mut();
    v_res_5104_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0(v_k_5096_, v_b_5097_, v_c_5098_, v___y_5099_, v___y_5100_, v___y_5101_, v___y_5102_);
    lean_dec(v___y_5102_);
    lean_dec_ref(v___y_5101_);
    lean_dec(v___y_5100_);
    lean_dec_ref(v___y_5099_);
    return v_res_5104_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(
    mut v_e_5105_: *mut LeanObject,
    mut v_k_5106_: *mut LeanObject,
    mut v_cleanupAnnotations_5107_: u8,
    mut v___y_5108_: *mut LeanObject,
    mut v___y_5109_: *mut LeanObject,
    mut v___y_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: u8 = 0;
    let mut v___x_5115_: u8 = 0;
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5121_: u8 = 0;
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5125_: u8 = 0;
    let mut v_a_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5129_: u8 = 0;
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5113_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_5113_, 0, v_k_5106_);
                v___x_5114_ = 1;
                v___x_5115_ = 0;
                v___x_5116_ = lean_box(0);
                v___x_5117_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_5117_) == 0 {
                    v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
                    v_isSharedCheck_5125_ = (!lean_is_exclusive(v___x_5117_)) as u8;
                    if v_isSharedCheck_5125_ == 0 {
                        v___x_5120_ = v___x_5117_;
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5118_);
                        lean_dec(v___x_5117_);
                        v___x_5120_ = lean_box(0);
                        v_isShared_5121_ = v_isSharedCheck_5125_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5126_ = lean_ctor_get(v___x_5117_, 0);
                    v_isSharedCheck_5133_ = (!lean_is_exclusive(v___x_5117_)) as u8;
                    if v_isSharedCheck_5133_ == 0 {
                        v___x_5128_ = v___x_5117_;
                        v_isShared_5129_ = v_isSharedCheck_5133_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5126_);
                        lean_dec(v___x_5117_);
                        v___x_5128_ = lean_box(0);
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
                    v_reuseFailAlloc_5124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
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
                    v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
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
    mut v_e_5134_: *mut LeanObject,
    mut v_k_5135_: *mut LeanObject,
    mut v_cleanupAnnotations_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
    mut v___y_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5142_: u8 = 0;
    let mut v_res_5143_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5142_ = (lean_unbox(v_cleanupAnnotations_5136_) as u8);
    v_res_5143_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_e_5134_, v_k_5135_, v_cleanupAnnotations_boxed_5142_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
    lean_dec(v___y_5140_);
    lean_dec_ref(v___y_5139_);
    lean_dec(v___y_5138_);
    lean_dec_ref(v___y_5137_);
    return v_res_5143_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1(
    mut v_00_u03b1_5144_: *mut LeanObject,
    mut v_e_5145_: *mut LeanObject,
    mut v_k_5146_: *mut LeanObject,
    mut v_cleanupAnnotations_5147_: u8,
    mut v___y_5148_: *mut LeanObject,
    mut v___y_5149_: *mut LeanObject,
    mut v___y_5150_: *mut LeanObject,
    mut v___y_5151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    v___x_5153_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_e_5145_, v_k_5146_, v_cleanupAnnotations_5147_, v___y_5148_, v___y_5149_, v___y_5150_, v___y_5151_);
    return v___x_5153_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___boxed(
    mut v_00_u03b1_5154_: *mut LeanObject,
    mut v_e_5155_: *mut LeanObject,
    mut v_k_5156_: *mut LeanObject,
    mut v_cleanupAnnotations_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
    mut v___y_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
    mut v___y_5162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5163_: u8 = 0;
    let mut v_res_5164_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5163_ = (lean_unbox(v_cleanupAnnotations_5157_) as u8);
    v_res_5164_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1(v_00_u03b1_5154_, v_e_5155_, v_k_5156_, v_cleanupAnnotations_boxed_5163_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
    lean_dec(v___y_5161_);
    lean_dec_ref(v___y_5160_);
    lean_dec(v___y_5159_);
    lean_dec_ref(v___y_5158_);
    return v_res_5164_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0___boxed(
    mut v_res_5168_: *mut LeanObject,
    mut v_values_5169_: *mut LeanObject,
    mut v_k_5170_: *mut LeanObject,
    mut v___x_5171_: *mut LeanObject,
    mut v_funType_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
    mut v___y_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
    mut v___y_5176_: *mut LeanObject,
    mut v___y_5177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5178_: *mut LeanObject = core::ptr::null_mut();
    v_res_5178_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0(v_res_5168_, v_values_5169_, v_k_5170_, v___x_5171_, v_funType_5172_, v___y_5173_, v___y_5174_, v___y_5175_, v___y_5176_);
    lean_dec(v___y_5176_);
    lean_dec_ref(v___y_5175_);
    lean_dec(v___y_5174_);
    lean_dec_ref(v___y_5173_);
    return v_res_5178_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1(
    mut v___x_5179_: u8,
    mut v_i_5180_: *mut LeanObject,
    mut v_res_5181_: *mut LeanObject,
    mut v_values_5182_: *mut LeanObject,
    mut v_k_5183_: *mut LeanObject,
    mut v_xs_5184_: *mut LeanObject,
    mut v_value_5185_: *mut LeanObject,
    mut v___y_5186_: *mut LeanObject,
    mut v___y_5187_: *mut LeanObject,
    mut v___y_5188_: *mut LeanObject,
    mut v___y_5189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: u8 = 0;
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: u8 = 0;
    let mut v___x_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5210_: u8 = 0;
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5214_: u8 = 0;
    let mut v_a_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5218_: u8 = 0;
    let mut v___x_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5222_: u8 = 0;
    let mut v_a_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5226_: u8 = 0;
    let mut v___x_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5189_);
                lean_inc_ref(v___y_5188_);
                lean_inc(v___y_5187_);
                lean_inc_ref(v___y_5186_);
                v___x_5191_ = lean_infer_type(
                    v_value_5185_,
                    v___y_5186_,
                    v___y_5187_,
                    v___y_5188_,
                    v___y_5189_,
                );
                if lean_obj_tag(v___x_5191_) == 0 {
                    v_a_5192_ = lean_ctor_get(v___x_5191_, 0);
                    lean_inc(v_a_5192_);
                    lean_dec_ref_known(v___x_5191_, 1);
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
                    if lean_obj_tag(v___x_5196_) == 0 {
                        v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
                        lean_inc_n(v_a_5197_, 2);
                        lean_dec_ref_known(v___x_5196_, 1);
                        lean_inc(v___y_5189_);
                        lean_inc_ref(v___y_5188_);
                        lean_inc(v___y_5187_);
                        lean_inc_ref(v___y_5186_);
                        v___x_5198_ = lean_infer_type(
                            v_a_5197_,
                            v___y_5186_,
                            v___y_5187_,
                            v___y_5188_,
                            v___y_5189_,
                        );
                        if lean_obj_tag(v___x_5198_) == 0 {
                            v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
                            lean_inc(v_a_5199_);
                            lean_dec_ref_known(v___x_5198_, 1);
                            v___x_5200_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___closed__1;
                            v___x_5201_ = lean_unsigned_to_nat(1);
                            v___x_5202_ = lean_nat_add(v_i_5180_, v___x_5201_);
                            lean_inc(v___x_5202_);
                            v___f_5203_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                            lean_closure_set(v___f_5203_, 0, v_res_5181_);
                            lean_closure_set(v___f_5203_, 1, v_values_5182_);
                            lean_closure_set(v___f_5203_, 2, v_k_5183_);
                            lean_closure_set(v___f_5203_, 3, v___x_5202_);
                            v___x_5204_ = lean_name_append_index_after(v___x_5200_, v___x_5202_);
                            v___x_5205_ = 0;
                            v___x_5206_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__0___redArg(v___x_5204_, v_a_5199_, v_a_5197_, v___f_5203_, v___x_5194_, v___x_5205_, v___y_5186_, v___y_5187_, v___y_5188_, v___y_5189_);
                            return v___x_5206_;
                        } else {
                            lean_dec(v_a_5197_);
                            lean_dec_ref(v_k_5183_);
                            lean_dec_ref(v_values_5182_);
                            lean_dec_ref(v_res_5181_);
                            v_a_5207_ = lean_ctor_get(v___x_5198_, 0);
                            v_isSharedCheck_5214_ = (!lean_is_exclusive(v___x_5198_)) as u8;
                            if v_isSharedCheck_5214_ == 0 {
                                v___x_5209_ = v___x_5198_;
                                v_isShared_5210_ = v_isSharedCheck_5214_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5207_);
                                lean_dec(v___x_5198_);
                                v___x_5209_ = lean_box(0);
                                v_isShared_5210_ = v_isSharedCheck_5214_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_k_5183_);
                        lean_dec_ref(v_values_5182_);
                        lean_dec_ref(v_res_5181_);
                        v_a_5215_ = lean_ctor_get(v___x_5196_, 0);
                        v_isSharedCheck_5222_ = (!lean_is_exclusive(v___x_5196_)) as u8;
                        if v_isSharedCheck_5222_ == 0 {
                            v___x_5217_ = v___x_5196_;
                            v_isShared_5218_ = v_isSharedCheck_5222_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5215_);
                            lean_dec(v___x_5196_);
                            v___x_5217_ = lean_box(0);
                            v_isShared_5218_ = v_isSharedCheck_5222_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_5183_);
                    lean_dec_ref(v_values_5182_);
                    lean_dec_ref(v_res_5181_);
                    v_a_5223_ = lean_ctor_get(v___x_5191_, 0);
                    v_isSharedCheck_5230_ = (!lean_is_exclusive(v___x_5191_)) as u8;
                    if v_isSharedCheck_5230_ == 0 {
                        v___x_5225_ = v___x_5191_;
                        v_isShared_5226_ = v_isSharedCheck_5230_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5223_);
                        lean_dec(v___x_5191_);
                        v___x_5225_ = lean_box(0);
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
                    v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
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
                    v_reuseFailAlloc_5221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5221_, 0, v_a_5215_);
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
                    v_reuseFailAlloc_5229_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5229_, 0, v_a_5223_);
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
    mut v___x_5231_: *mut LeanObject,
    mut v_i_5232_: *mut LeanObject,
    mut v_res_5233_: *mut LeanObject,
    mut v_values_5234_: *mut LeanObject,
    mut v_k_5235_: *mut LeanObject,
    mut v_xs_5236_: *mut LeanObject,
    mut v_value_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
    mut v___y_5241_: *mut LeanObject,
    mut v___y_5242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1255__boxed_5243_: u8 = 0;
    let mut v_res_5244_: *mut LeanObject = core::ptr::null_mut();
    v___x_1255__boxed_5243_ = (lean_unbox(v___x_5231_) as u8);
    v_res_5244_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1(v___x_1255__boxed_5243_, v_i_5232_, v_res_5233_, v_values_5234_, v_k_5235_, v_xs_5236_, v_value_5237_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_);
    lean_dec(v___y_5241_);
    lean_dec_ref(v___y_5240_);
    lean_dec(v___y_5239_);
    lean_dec_ref(v___y_5238_);
    lean_dec_ref(v_xs_5236_);
    lean_dec(v_i_5232_);
    return v_res_5244_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(
    mut v_values_5245_: *mut LeanObject,
    mut v_k_5246_: *mut LeanObject,
    mut v_i_5247_: *mut LeanObject,
    mut v_res_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
    mut v_a_5250_: *mut LeanObject,
    mut v_a_5251_: *mut LeanObject,
    mut v_a_5252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: u8 = 0;
    v___x_5254_ = lean_array_get_size(v_values_5245_);
    v___x_5255_ = lean_nat_dec_lt(v_i_5247_, v___x_5254_);
    if v___x_5255_ == 0 {
        let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_5247_);
        lean_dec_ref(v_values_5245_);
        lean_inc(v_a_5252_);
        lean_inc_ref(v_a_5251_);
        lean_inc(v_a_5250_);
        lean_inc_ref(v_a_5249_);
        v___x_5256_ = lean_apply_6(
            v_k_5246_,
            v_res_5248_,
            v_a_5249_,
            v_a_5250_,
            v_a_5251_,
            v_a_5252_,
            lean_box(0),
        );
        return v___x_5256_;
    } else {
        let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_5258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5260_: u8 = 0;
        let mut v___x_5261_: *mut LeanObject = core::ptr::null_mut();
        v___x_5257_ = lean_box((v___x_5255_) as usize);
        lean_inc_ref(v_values_5245_);
        lean_inc(v_i_5247_);
        v___f_5258_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__1___boxed as *mut core::ffi::c_void, 12, 5);
        lean_closure_set(v___f_5258_, 0, v___x_5257_);
        lean_closure_set(v___f_5258_, 1, v_i_5247_);
        lean_closure_set(v___f_5258_, 2, v_res_5248_);
        lean_closure_set(v___f_5258_, 3, v_values_5245_);
        lean_closure_set(v___f_5258_, 4, v_k_5246_);
        v___x_5259_ = lean_array_fget(v_values_5245_, v_i_5247_);
        lean_dec(v_i_5247_);
        lean_dec_ref(v_values_5245_);
        v___x_5260_ = 0;
        v___x_5261_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v___x_5259_, v___f_5258_, v___x_5260_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_);
        return v___x_5261_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___lam__0(
    mut v_res_5262_: *mut LeanObject,
    mut v_values_5263_: *mut LeanObject,
    mut v_k_5264_: *mut LeanObject,
    mut v___x_5265_: *mut LeanObject,
    mut v_funType_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
    mut v___y_5270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    v___x_5272_ = lean_array_push(v_res_5262_, v_funType_5266_);
    v___x_5273_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5263_, v_k_5264_, v___x_5265_, v___x_5272_, v___y_5267_, v___y_5268_, v___y_5269_, v___y_5270_);
    return v___x_5273_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg___boxed(
    mut v_values_5274_: *mut LeanObject,
    mut v_k_5275_: *mut LeanObject,
    mut v_i_5276_: *mut LeanObject,
    mut v_res_5277_: *mut LeanObject,
    mut v_a_5278_: *mut LeanObject,
    mut v_a_5279_: *mut LeanObject,
    mut v_a_5280_: *mut LeanObject,
    mut v_a_5281_: *mut LeanObject,
    mut v_a_5282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5283_: *mut LeanObject = core::ptr::null_mut();
    v_res_5283_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5274_, v_k_5275_, v_i_5276_, v_res_5277_, v_a_5278_, v_a_5279_, v_a_5280_, v_a_5281_);
    lean_dec(v_a_5281_);
    lean_dec_ref(v_a_5280_);
    lean_dec(v_a_5279_);
    lean_dec_ref(v_a_5278_);
    return v_res_5283_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go(
    mut v_00_u03b1_5284_: *mut LeanObject,
    mut v_values_5285_: *mut LeanObject,
    mut v_k_5286_: *mut LeanObject,
    mut v_i_5287_: *mut LeanObject,
    mut v_res_5288_: *mut LeanObject,
    mut v_a_5289_: *mut LeanObject,
    mut v_a_5290_: *mut LeanObject,
    mut v_a_5291_: *mut LeanObject,
    mut v_a_5292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    v___x_5294_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5285_, v_k_5286_, v_i_5287_, v_res_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_);
    return v___x_5294_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___boxed(
    mut v_00_u03b1_5295_: *mut LeanObject,
    mut v_values_5296_: *mut LeanObject,
    mut v_k_5297_: *mut LeanObject,
    mut v_i_5298_: *mut LeanObject,
    mut v_res_5299_: *mut LeanObject,
    mut v_a_5300_: *mut LeanObject,
    mut v_a_5301_: *mut LeanObject,
    mut v_a_5302_: *mut LeanObject,
    mut v_a_5303_: *mut LeanObject,
    mut v_a_5304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5305_: *mut LeanObject = core::ptr::null_mut();
    v_res_5305_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go(v_00_u03b1_5295_, v_values_5296_, v_k_5297_, v_i_5298_, v_res_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_);
    lean_dec(v_a_5303_);
    lean_dec_ref(v_a_5302_);
    lean_dec(v_a_5301_);
    lean_dec_ref(v_a_5300_);
    return v_res_5305_;
}
pub unsafe fn l_Lean_Elab_Structural_withFunTypes___redArg(
    mut v_values_5306_: *mut LeanObject,
    mut v_k_5307_: *mut LeanObject,
    mut v_a_5308_: *mut LeanObject,
    mut v_a_5309_: *mut LeanObject,
    mut v_a_5310_: *mut LeanObject,
    mut v_a_5311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    v___x_5313_ = lean_unsigned_to_nat(0);
    v___x_5314_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApp___closed__5;
    v___x_5315_ = l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go___redArg(v_values_5306_, v_k_5307_, v___x_5313_, v___x_5314_, v_a_5308_, v_a_5309_, v_a_5310_, v_a_5311_);
    return v___x_5315_;
}
pub unsafe fn l_Lean_Elab_Structural_withFunTypes___redArg___boxed(
    mut v_values_5316_: *mut LeanObject,
    mut v_k_5317_: *mut LeanObject,
    mut v_a_5318_: *mut LeanObject,
    mut v_a_5319_: *mut LeanObject,
    mut v_a_5320_: *mut LeanObject,
    mut v_a_5321_: *mut LeanObject,
    mut v_a_5322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5323_: *mut LeanObject = core::ptr::null_mut();
    v_res_5323_ = l_Lean_Elab_Structural_withFunTypes___redArg(
        v_values_5316_,
        v_k_5317_,
        v_a_5318_,
        v_a_5319_,
        v_a_5320_,
        v_a_5321_,
    );
    lean_dec(v_a_5321_);
    lean_dec_ref(v_a_5320_);
    lean_dec(v_a_5319_);
    lean_dec_ref(v_a_5318_);
    return v_res_5323_;
}
pub unsafe fn l_Lean_Elab_Structural_withFunTypes(
    mut v_00_u03b1_5324_: *mut LeanObject,
    mut v_values_5325_: *mut LeanObject,
    mut v_k_5326_: *mut LeanObject,
    mut v_a_5327_: *mut LeanObject,
    mut v_a_5328_: *mut LeanObject,
    mut v_a_5329_: *mut LeanObject,
    mut v_a_5330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5333_: *mut LeanObject,
    mut v_values_5334_: *mut LeanObject,
    mut v_k_5335_: *mut LeanObject,
    mut v_a_5336_: *mut LeanObject,
    mut v_a_5337_: *mut LeanObject,
    mut v_a_5338_: *mut LeanObject,
    mut v_a_5339_: *mut LeanObject,
    mut v_a_5340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5341_: *mut LeanObject = core::ptr::null_mut();
    v_res_5341_ = l_Lean_Elab_Structural_withFunTypes(
        v_00_u03b1_5333_,
        v_values_5334_,
        v_k_5335_,
        v_a_5336_,
        v_a_5337_,
        v_a_5338_,
        v_a_5339_,
    );
    lean_dec(v_a_5339_);
    lean_dec_ref(v_a_5338_);
    lean_dec(v_a_5337_);
    lean_dec_ref(v_a_5336_);
    return v_res_5341_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive___lam__0(
    mut v_funType_5342_: *mut LeanObject,
    mut v_recArgInfo_5343_: *mut LeanObject,
    mut v_xs_5344_: *mut LeanObject,
    mut v_x_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
    mut v___y_5347_: *mut LeanObject,
    mut v___y_5348_: *mut LeanObject,
    mut v___y_5349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: u8 = 0;
    let mut v___x_5356_: u8 = 0;
    let mut v___x_5357_: u8 = 0;
    let mut v___x_5358_: *mut LeanObject = core::ptr::null_mut();
    v_type_5351_ = l_Lean_mkAppN(v_funType_5342_, v_xs_5344_);
    v___x_5352_ =
        l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(v_recArgInfo_5343_, v_xs_5344_);
    v_fst_5353_ = lean_ctor_get(v___x_5352_, 0);
    lean_inc(v_fst_5353_);
    v_snd_5354_ = lean_ctor_get(v___x_5352_, 1);
    lean_inc(v_snd_5354_);
    lean_dec_ref(v___x_5352_);
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
    lean_dec(v_snd_5354_);
    if lean_obj_tag(v___x_5358_) == 0 {
        let mut v_a_5359_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
        v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
        lean_inc(v_a_5359_);
        lean_dec_ref_known(v___x_5358_, 1);
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
        lean_dec(v_fst_5353_);
        return v___x_5360_;
    } else {
        lean_dec(v_fst_5353_);
        return v___x_5358_;
    }
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive___lam__0___boxed(
    mut v_funType_5361_: *mut LeanObject,
    mut v_recArgInfo_5362_: *mut LeanObject,
    mut v_xs_5363_: *mut LeanObject,
    mut v_x_5364_: *mut LeanObject,
    mut v___y_5365_: *mut LeanObject,
    mut v___y_5366_: *mut LeanObject,
    mut v___y_5367_: *mut LeanObject,
    mut v___y_5368_: *mut LeanObject,
    mut v___y_5369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5370_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5368_);
    lean_dec_ref(v___y_5367_);
    lean_dec(v___y_5366_);
    lean_dec_ref(v___y_5365_);
    lean_dec_ref(v_x_5364_);
    return v_res_5370_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive(
    mut v_recArgInfo_5371_: *mut LeanObject,
    mut v_value_5372_: *mut LeanObject,
    mut v_funType_5373_: *mut LeanObject,
    mut v_a_5374_: *mut LeanObject,
    mut v_a_5375_: *mut LeanObject,
    mut v_a_5376_: *mut LeanObject,
    mut v_a_5377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: u8 = 0;
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    v___f_5379_ = lean_alloc_closure(
        l_Lean_Elab_Structural_mkIndPredBRecOnMotive___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    lean_closure_set(v___f_5379_, 0, v_funType_5373_);
    lean_closure_set(v___f_5379_, 1, v_recArgInfo_5371_);
    v___x_5380_ = 0;
    v___x_5381_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_value_5372_, v___f_5379_, v___x_5380_, v_a_5374_, v_a_5375_, v_a_5376_, v_a_5377_);
    return v___x_5381_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnMotive___boxed(
    mut v_recArgInfo_5382_: *mut LeanObject,
    mut v_value_5383_: *mut LeanObject,
    mut v_funType_5384_: *mut LeanObject,
    mut v_a_5385_: *mut LeanObject,
    mut v_a_5386_: *mut LeanObject,
    mut v_a_5387_: *mut LeanObject,
    mut v_a_5388_: *mut LeanObject,
    mut v_a_5389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5390_: *mut LeanObject = core::ptr::null_mut();
    v_res_5390_ = l_Lean_Elab_Structural_mkIndPredBRecOnMotive(
        v_recArgInfo_5382_,
        v_value_5383_,
        v_funType_5384_,
        v_a_5385_,
        v_a_5386_,
        v_a_5387_,
        v_a_5388_,
    );
    lean_dec(v_a_5388_);
    lean_dec_ref(v_a_5387_);
    lean_dec(v_a_5386_);
    lean_dec_ref(v_a_5385_);
    return v_res_5390_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(
    mut v___y_5391_: *mut LeanObject,
    mut v_auxDeclNGen_5392_: *mut LeanObject,
    mut v_a_x3f_5393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5406_: u8 = 0;
    let mut v___x_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5413_: u8 = 0;
    let mut v_unused_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5395_ = lean_st_ref_take(v___y_5391_);
                v_env_5396_ = lean_ctor_get(v___x_5395_, 0);
                v_nextMacroScope_5397_ = lean_ctor_get(v___x_5395_, 1);
                v_ngen_5398_ = lean_ctor_get(v___x_5395_, 2);
                v_traceState_5399_ = lean_ctor_get(v___x_5395_, 4);
                v_cache_5400_ = lean_ctor_get(v___x_5395_, 5);
                v_messages_5401_ = lean_ctor_get(v___x_5395_, 6);
                v_infoState_5402_ = lean_ctor_get(v___x_5395_, 7);
                v_snapshotTasks_5403_ = lean_ctor_get(v___x_5395_, 8);
                v_isSharedCheck_5413_ = (!lean_is_exclusive(v___x_5395_)) as u8;
                if v_isSharedCheck_5413_ == 0 {
                    v_unused_5414_ = lean_ctor_get(v___x_5395_, 3);
                    lean_dec(v_unused_5414_);
                    v___x_5405_ = v___x_5395_;
                    v_isShared_5406_ = v_isSharedCheck_5413_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5403_);
                    lean_inc(v_infoState_5402_);
                    lean_inc(v_messages_5401_);
                    lean_inc(v_cache_5400_);
                    lean_inc(v_traceState_5399_);
                    lean_inc(v_ngen_5398_);
                    lean_inc(v_nextMacroScope_5397_);
                    lean_inc(v_env_5396_);
                    lean_dec(v___x_5395_);
                    v___x_5405_ = lean_box(0);
                    v_isShared_5406_ = v_isSharedCheck_5413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_5406_ == 0 {
                    lean_ctor_set(v___x_5405_, 3, v_auxDeclNGen_5392_);
                    v___x_5408_ = v___x_5405_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5412_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 0, v_env_5396_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 1, v_nextMacroScope_5397_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 2, v_ngen_5398_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 3, v_auxDeclNGen_5392_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 4, v_traceState_5399_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 5, v_cache_5400_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 6, v_messages_5401_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 7, v_infoState_5402_);
                    lean_ctor_set(v_reuseFailAlloc_5412_, 8, v_snapshotTasks_5403_);
                    v___x_5408_ = v_reuseFailAlloc_5412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5409_ = lean_st_ref_set(v___y_5391_, v___x_5408_);
                v___x_5410_ = lean_box(0);
                v___x_5411_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5411_, 0, v___x_5410_);
                return v___x_5411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0___boxed(
    mut v___y_5415_: *mut LeanObject,
    mut v_auxDeclNGen_5416_: *mut LeanObject,
    mut v_a_x3f_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5419_: *mut LeanObject = core::ptr::null_mut();
    v_res_5419_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(v___y_5415_, v_auxDeclNGen_5416_, v_a_x3f_5417_);
    lean_dec(v_a_x3f_5417_);
    lean_dec(v___y_5415_);
    return v_res_5419_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(
    mut v_name_5420_: *mut LeanObject,
    mut v_x_5421_: *mut LeanObject,
    mut v___y_5422_: *mut LeanObject,
    mut v___y_5423_: *mut LeanObject,
    mut v___y_5424_: *mut LeanObject,
    mut v___y_5425_: *mut LeanObject,
    mut v___y_5426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: u8 = 0;
    let mut v___x_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5454_: u8 = 0;
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5460_: u8 = 0;
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5464_: u8 = 0;
    let mut v_unused_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v_a_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5473_: u8 = 0;
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut v_unused_5478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5480_: u8 = 0;
    let mut v_unused_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5428_ = lean_st_ref_get(v___y_5426_);
                v_auxDeclNGen_5429_ = lean_ctor_get(v___x_5428_, 3);
                lean_inc_ref(v_auxDeclNGen_5429_);
                lean_dec(v___x_5428_);
                v_namePrefix_5430_ = lean_ctor_get(v_auxDeclNGen_5429_, 0);
                v___x_5431_ = lean_name_eq(v_namePrefix_5430_, v_name_5420_);
                if v___x_5431_ == 0 {
                    v___x_5432_ = lean_st_ref_take(v___y_5426_);
                    v_env_5433_ = lean_ctor_get(v___x_5432_, 0);
                    v_nextMacroScope_5434_ = lean_ctor_get(v___x_5432_, 1);
                    v_ngen_5435_ = lean_ctor_get(v___x_5432_, 2);
                    v_traceState_5436_ = lean_ctor_get(v___x_5432_, 4);
                    v_cache_5437_ = lean_ctor_get(v___x_5432_, 5);
                    v_messages_5438_ = lean_ctor_get(v___x_5432_, 6);
                    v_infoState_5439_ = lean_ctor_get(v___x_5432_, 7);
                    v_snapshotTasks_5440_ = lean_ctor_get(v___x_5432_, 8);
                    v_isSharedCheck_5480_ = (!lean_is_exclusive(v___x_5432_)) as u8;
                    if v_isSharedCheck_5480_ == 0 {
                        v_unused_5481_ = lean_ctor_get(v___x_5432_, 3);
                        lean_dec(v_unused_5481_);
                        v___x_5442_ = v___x_5432_;
                        v_isShared_5443_ = v_isSharedCheck_5480_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_5440_);
                        lean_inc(v_infoState_5439_);
                        lean_inc(v_messages_5438_);
                        lean_inc(v_cache_5437_);
                        lean_inc(v_traceState_5436_);
                        lean_inc(v_ngen_5435_);
                        lean_inc(v_nextMacroScope_5434_);
                        lean_inc(v_env_5433_);
                        lean_dec(v___x_5432_);
                        v___x_5442_ = lean_box(0);
                        v_isShared_5443_ = v_isSharedCheck_5480_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_auxDeclNGen_5429_);
                    lean_dec(v_name_5420_);
                    lean_inc(v___y_5426_);
                    lean_inc_ref(v___y_5425_);
                    lean_inc(v___y_5424_);
                    lean_inc_ref(v___y_5423_);
                    lean_inc(v___y_5422_);
                    v___x_5482_ = lean_apply_6(
                        v_x_5421_,
                        v___y_5422_,
                        v___y_5423_,
                        v___y_5424_,
                        v___y_5425_,
                        v___y_5426_,
                        lean_box(0),
                    );
                    return v___x_5482_;
                }
            }
            1 => {
                v___x_5444_ = lean_unsigned_to_nat(1);
                v___x_5445_ = lean_box(0);
                v___x_5446_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5446_, 0, v_name_5420_);
                lean_ctor_set(v___x_5446_, 1, v___x_5444_);
                lean_ctor_set(v___x_5446_, 2, v___x_5445_);
                if v_isShared_5443_ == 0 {
                    lean_ctor_set(v___x_5442_, 3, v___x_5446_);
                    v___x_5448_ = v___x_5442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5479_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 0, v_env_5433_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 1, v_nextMacroScope_5434_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 2, v_ngen_5435_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 3, v___x_5446_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 4, v_traceState_5436_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 5, v_cache_5437_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 6, v_messages_5438_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 7, v_infoState_5439_);
                    lean_ctor_set(v_reuseFailAlloc_5479_, 8, v_snapshotTasks_5440_);
                    v___x_5448_ = v_reuseFailAlloc_5479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5449_ = lean_st_ref_set(v___y_5426_, v___x_5448_);
                lean_inc(v___y_5426_);
                lean_inc_ref(v___y_5425_);
                lean_inc(v___y_5424_);
                lean_inc_ref(v___y_5423_);
                lean_inc(v___y_5422_);
                v___x_5450_ = lean_apply_6(
                    v_x_5421_,
                    v___y_5422_,
                    v___y_5423_,
                    v___y_5424_,
                    v___y_5425_,
                    v___y_5426_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_5450_) == 0 {
                    v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
                    v_isSharedCheck_5467_ = (!lean_is_exclusive(v___x_5450_)) as u8;
                    if v_isSharedCheck_5467_ == 0 {
                        v___x_5453_ = v___x_5450_;
                        v_isShared_5454_ = v_isSharedCheck_5467_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5451_);
                        lean_dec(v___x_5450_);
                        v___x_5453_ = lean_box(0);
                        v_isShared_5454_ = v_isSharedCheck_5467_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_5468_ = lean_ctor_get(v___x_5450_, 0);
                    lean_inc(v_a_5468_);
                    lean_dec_ref_known(v___x_5450_, 1);
                    v___x_5469_ = lean_box(0);
                    v___x_5470_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(v___y_5426_, v_auxDeclNGen_5429_, v___x_5469_);
                    v_isSharedCheck_5477_ = (!lean_is_exclusive(v___x_5470_)) as u8;
                    if v_isSharedCheck_5477_ == 0 {
                        v_unused_5478_ = lean_ctor_get(v___x_5470_, 0);
                        lean_dec(v_unused_5478_);
                        v___x_5472_ = v___x_5470_;
                        v_isShared_5473_ = v_isSharedCheck_5477_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_5470_);
                        v___x_5472_ = lean_box(0);
                        v_isShared_5473_ = v_isSharedCheck_5477_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_5451_);
                if v_isShared_5454_ == 0 {
                    lean_ctor_set_tag(v___x_5453_, 1);
                    v___x_5456_ = v___x_5453_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5451_);
                    v___x_5456_ = v_reuseFailAlloc_5466_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5457_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg___lam__0(v___y_5426_, v_auxDeclNGen_5429_, v___x_5456_);
                lean_dec_ref(v___x_5456_);
                v_isSharedCheck_5464_ = (!lean_is_exclusive(v___x_5457_)) as u8;
                if v_isSharedCheck_5464_ == 0 {
                    v_unused_5465_ = lean_ctor_get(v___x_5457_, 0);
                    lean_dec(v_unused_5465_);
                    v___x_5459_ = v___x_5457_;
                    v_isShared_5460_ = v_isSharedCheck_5464_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_5457_);
                    v___x_5459_ = lean_box(0);
                    v_isShared_5460_ = v_isSharedCheck_5464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_5460_ == 0 {
                    lean_ctor_set(v___x_5459_, 0, v_a_5451_);
                    v___x_5462_ = v___x_5459_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5451_);
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
                    lean_ctor_set_tag(v___x_5472_, 1);
                    lean_ctor_set(v___x_5472_, 0, v_a_5468_);
                    v___x_5475_ = v___x_5472_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5468_);
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
    mut v_name_5483_: *mut LeanObject,
    mut v_x_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
    mut v___y_5487_: *mut LeanObject,
    mut v___y_5488_: *mut LeanObject,
    mut v___y_5489_: *mut LeanObject,
    mut v___y_5490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5491_: *mut LeanObject = core::ptr::null_mut();
    v_res_5491_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(v_name_5483_, v_x_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
    lean_dec(v___y_5489_);
    lean_dec_ref(v___y_5488_);
    lean_dec(v___y_5487_);
    lean_dec_ref(v___y_5486_);
    lean_dec(v___y_5485_);
    return v_res_5491_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0(
    mut v_00_u03b1_5492_: *mut LeanObject,
    mut v_name_5493_: *mut LeanObject,
    mut v_x_5494_: *mut LeanObject,
    mut v___y_5495_: *mut LeanObject,
    mut v___y_5496_: *mut LeanObject,
    mut v___y_5497_: *mut LeanObject,
    mut v___y_5498_: *mut LeanObject,
    mut v___y_5499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5501_: *mut LeanObject = core::ptr::null_mut();
    v___x_5501_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(v_name_5493_, v_x_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_);
    return v___x_5501_;
}
pub unsafe fn l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___boxed(
    mut v_00_u03b1_5502_: *mut LeanObject,
    mut v_name_5503_: *mut LeanObject,
    mut v_x_5504_: *mut LeanObject,
    mut v___y_5505_: *mut LeanObject,
    mut v___y_5506_: *mut LeanObject,
    mut v___y_5507_: *mut LeanObject,
    mut v___y_5508_: *mut LeanObject,
    mut v___y_5509_: *mut LeanObject,
    mut v___y_5510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5511_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5509_);
    lean_dec_ref(v___y_5508_);
    lean_dec(v___y_5507_);
    lean_dec_ref(v___y_5506_);
    lean_dec(v___y_5505_);
    return v_res_5511_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(
    mut v_type_5512_: *mut LeanObject,
    mut v_maxFVars_x3f_5513_: *mut LeanObject,
    mut v_k_5514_: *mut LeanObject,
    mut v_cleanupAnnotations_5515_: u8,
    mut v_whnfType_5516_: u8,
    mut v___y_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
    mut v___y_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5527_: u8 = 0;
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5531_: u8 = 0;
    let mut v_a_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5535_: u8 = 0;
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_5522_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_5522_, 0, v_k_5514_);
                v___x_5523_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
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
                if lean_obj_tag(v___x_5523_) == 0 {
                    v_a_5524_ = lean_ctor_get(v___x_5523_, 0);
                    v_isSharedCheck_5531_ = (!lean_is_exclusive(v___x_5523_)) as u8;
                    if v_isSharedCheck_5531_ == 0 {
                        v___x_5526_ = v___x_5523_;
                        v_isShared_5527_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5524_);
                        lean_dec(v___x_5523_);
                        v___x_5526_ = lean_box(0);
                        v_isShared_5527_ = v_isSharedCheck_5531_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5532_ = lean_ctor_get(v___x_5523_, 0);
                    v_isSharedCheck_5539_ = (!lean_is_exclusive(v___x_5523_)) as u8;
                    if v_isSharedCheck_5539_ == 0 {
                        v___x_5534_ = v___x_5523_;
                        v_isShared_5535_ = v_isSharedCheck_5539_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5532_);
                        lean_dec(v___x_5523_);
                        v___x_5534_ = lean_box(0);
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
                    v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5530_, 0, v_a_5524_);
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
                    v_reuseFailAlloc_5538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5538_, 0, v_a_5532_);
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
    mut v_type_5540_: *mut LeanObject,
    mut v_maxFVars_x3f_5541_: *mut LeanObject,
    mut v_k_5542_: *mut LeanObject,
    mut v_cleanupAnnotations_5543_: *mut LeanObject,
    mut v_whnfType_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
    mut v___y_5547_: *mut LeanObject,
    mut v___y_5548_: *mut LeanObject,
    mut v___y_5549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5550_: u8 = 0;
    let mut v_whnfType_boxed_5551_: u8 = 0;
    let mut v_res_5552_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5550_ = (lean_unbox(v_cleanupAnnotations_5543_) as u8);
    v_whnfType_boxed_5551_ = (lean_unbox(v_whnfType_5544_) as u8);
    v_res_5552_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(v_type_5540_, v_maxFVars_x3f_5541_, v_k_5542_, v_cleanupAnnotations_boxed_5550_, v_whnfType_boxed_5551_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_);
    lean_dec(v___y_5548_);
    lean_dec_ref(v___y_5547_);
    lean_dec(v___y_5546_);
    lean_dec_ref(v___y_5545_);
    return v_res_5552_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1(
    mut v_00_u03b1_5553_: *mut LeanObject,
    mut v_type_5554_: *mut LeanObject,
    mut v_maxFVars_x3f_5555_: *mut LeanObject,
    mut v_k_5556_: *mut LeanObject,
    mut v_cleanupAnnotations_5557_: u8,
    mut v_whnfType_5558_: u8,
    mut v___y_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    v___x_5564_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(v_type_5554_, v_maxFVars_x3f_5555_, v_k_5556_, v_cleanupAnnotations_5557_, v_whnfType_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_);
    return v___x_5564_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___boxed(
    mut v_00_u03b1_5565_: *mut LeanObject,
    mut v_type_5566_: *mut LeanObject,
    mut v_maxFVars_x3f_5567_: *mut LeanObject,
    mut v_k_5568_: *mut LeanObject,
    mut v_cleanupAnnotations_5569_: *mut LeanObject,
    mut v_whnfType_5570_: *mut LeanObject,
    mut v___y_5571_: *mut LeanObject,
    mut v___y_5572_: *mut LeanObject,
    mut v___y_5573_: *mut LeanObject,
    mut v___y_5574_: *mut LeanObject,
    mut v___y_5575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_5576_: u8 = 0;
    let mut v_whnfType_boxed_5577_: u8 = 0;
    let mut v_res_5578_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_5576_ = (lean_unbox(v_cleanupAnnotations_5569_) as u8);
    v_whnfType_boxed_5577_ = (lean_unbox(v_whnfType_5570_) as u8);
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
    lean_dec(v___y_5574_);
    lean_dec_ref(v___y_5573_);
    lean_dec(v___y_5572_);
    lean_dec_ref(v___y_5571_);
    return v_res_5578_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0(
    mut v___x_5581_: *mut LeanObject,
    mut v_recArgInfo_5582_: *mut LeanObject,
    mut v_fst_5583_: *mut LeanObject,
    mut v_recArgInfos_5584_: *mut LeanObject,
    mut v_positions_5585_: *mut LeanObject,
    mut v_params_5586_: *mut LeanObject,
    mut v_value_5587_: *mut LeanObject,
    mut v_snd_5588_: *mut LeanObject,
    mut v_below_5589_: *mut LeanObject,
    mut v_x_5590_: *mut LeanObject,
    mut v___y_5591_: *mut LeanObject,
    mut v___y_5592_: *mut LeanObject,
    mut v___y_5593_: *mut LeanObject,
    mut v___y_5594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fnName_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: u8 = 0;
    let mut v___x_5624_: u8 = 0;
    let mut v___x_5625_: u8 = 0;
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5630_: u8 = 0;
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5635_: u8 = 0;
    let mut v_a_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5639_: u8 = 0;
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5643_: u8 = 0;
    let mut v_a_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5647_: u8 = 0;
    let mut v___x_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5651_: u8 = 0;
    let mut v_a_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5655_: u8 = 0;
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5659_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5596_ = lean_unsigned_to_nat(0);
                v___x_5597_ = lean_array_get_borrowed(v___x_5581_, v_below_5589_, v___x_5596_);
                lean_inc(v___y_5594_);
                lean_inc_ref(v___y_5593_);
                lean_inc(v___y_5592_);
                lean_inc_ref(v___y_5591_);
                lean_inc(v___x_5597_);
                v___x_5598_ = lean_infer_type(
                    v___x_5597_,
                    v___y_5591_,
                    v___y_5592_,
                    v___y_5593_,
                    v___y_5594_,
                );
                if lean_obj_tag(v___x_5598_) == 0 {
                    v_a_5599_ = lean_ctor_get(v___x_5598_, 0);
                    lean_inc(v_a_5599_);
                    lean_dec_ref_known(v___x_5598_, 1);
                    v___x_5600_ = l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___closed__0;
                    v___x_5601_ = lean_st_mk_ref(v___x_5600_);
                    v_fnName_5602_ = lean_ctor_get(v_recArgInfo_5582_, 0);
                    lean_inc(v_fnName_5602_);
                    lean_dec_ref(v_recArgInfo_5582_);
                    v___x_5603_ = lean_box(1);
                    v___x_5604_ = l_Lean_Expr_getForallBody(v_a_5599_);
                    lean_dec(v_a_5599_);
                    v___x_5605_ = l_Lean_Expr_getAppFn(v___x_5604_);
                    lean_dec_ref(v___x_5604_);
                    v___x_5606_ = l_Lean_Expr_constName_x21(v___x_5605_);
                    lean_dec_ref(v___x_5605_);
                    v___x_5607_ = lean_array_get_size(v_fst_5583_);
                    v___x_5608_ = lean_unsigned_to_nat(1);
                    v___x_5609_ = lean_nat_sub(v___x_5607_, v___x_5608_);
                    v___x_5610_ = lean_array_get_borrowed(v___x_5581_, v_fst_5583_, v___x_5609_);
                    lean_dec(v___x_5609_);
                    v___x_5611_ = l_Lean_Expr_fvarId_x21(v___x_5610_);
                    lean_inc(v___x_5597_);
                    v___x_5612_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5612_, 0, v___x_5606_);
                    lean_ctor_set(v___x_5612_, 1, v___x_5597_);
                    v___x_5613_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v___x_5611_, v___x_5612_, v___x_5603_);
                    v___x_5614_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5614_, 0, v___x_5613_);
                    lean_ctor_set(v___x_5614_, 1, v___x_5603_);
                    v___x_5615_ = lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_replaceIndPredRecApps___boxed as *mut core::ffi::c_void, 11, 5);
                    lean_closure_set(v___x_5615_, 0, v_recArgInfos_5584_);
                    lean_closure_set(v___x_5615_, 1, v_positions_5585_);
                    lean_closure_set(v___x_5615_, 2, v_params_5586_);
                    lean_closure_set(v___x_5615_, 3, v___x_5614_);
                    lean_closure_set(v___x_5615_, 4, v_value_5587_);
                    v___x_5616_ = l_Lean_withDeclNameForAuxNaming___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__0___redArg(v_fnName_5602_, v___x_5615_, v___x_5601_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_);
                    if lean_obj_tag(v___x_5616_) == 0 {
                        v_a_5617_ = lean_ctor_get(v___x_5616_, 0);
                        lean_inc(v_a_5617_);
                        lean_dec_ref_known(v___x_5616_, 1);
                        v___x_5618_ = lean_st_ref_get(v___x_5601_);
                        lean_dec(v___x_5601_);
                        v___x_5619_ = lean_mk_empty_array_with_capacity(v___x_5608_);
                        lean_inc(v___x_5597_);
                        v___x_5620_ = lean_array_push(v___x_5619_, v___x_5597_);
                        v___x_5621_ = l_Array_append___redArg(v_fst_5583_, v___x_5620_);
                        lean_dec_ref(v___x_5620_);
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
                        lean_dec_ref(v___x_5622_);
                        if lean_obj_tag(v___x_5626_) == 0 {
                            v_a_5627_ = lean_ctor_get(v___x_5626_, 0);
                            v_isSharedCheck_5635_ = (!lean_is_exclusive(v___x_5626_)) as u8;
                            if v_isSharedCheck_5635_ == 0 {
                                v___x_5629_ = v___x_5626_;
                                v_isShared_5630_ = v_isSharedCheck_5635_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_5627_);
                                lean_dec(v___x_5626_);
                                v___x_5629_ = lean_box(0);
                                v_isShared_5630_ = v_isSharedCheck_5635_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_5618_);
                            v_a_5636_ = lean_ctor_get(v___x_5626_, 0);
                            v_isSharedCheck_5643_ = (!lean_is_exclusive(v___x_5626_)) as u8;
                            if v_isSharedCheck_5643_ == 0 {
                                v___x_5638_ = v___x_5626_;
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_5636_);
                                lean_dec(v___x_5626_);
                                v___x_5638_ = lean_box(0);
                                v_isShared_5639_ = v_isSharedCheck_5643_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_5601_);
                        lean_dec_ref(v_fst_5583_);
                        v_a_5644_ = lean_ctor_get(v___x_5616_, 0);
                        v_isSharedCheck_5651_ = (!lean_is_exclusive(v___x_5616_)) as u8;
                        if v_isSharedCheck_5651_ == 0 {
                            v___x_5646_ = v___x_5616_;
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_5644_);
                            lean_dec(v___x_5616_);
                            v___x_5646_ = lean_box(0);
                            v_isShared_5647_ = v_isSharedCheck_5651_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_value_5587_);
                    lean_dec_ref(v_params_5586_);
                    lean_dec_ref(v_positions_5585_);
                    lean_dec_ref(v_recArgInfos_5584_);
                    lean_dec_ref(v_fst_5583_);
                    lean_dec_ref(v_recArgInfo_5582_);
                    v_a_5652_ = lean_ctor_get(v___x_5598_, 0);
                    v_isSharedCheck_5659_ = (!lean_is_exclusive(v___x_5598_)) as u8;
                    if v_isSharedCheck_5659_ == 0 {
                        v___x_5654_ = v___x_5598_;
                        v_isShared_5655_ = v_isSharedCheck_5659_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_5652_);
                        lean_dec(v___x_5598_);
                        v___x_5654_ = lean_box(0);
                        v_isShared_5655_ = v_isSharedCheck_5659_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5631_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5631_, 0, v_a_5627_);
                lean_ctor_set(v___x_5631_, 1, v___x_5618_);
                if v_isShared_5630_ == 0 {
                    lean_ctor_set(v___x_5629_, 0, v___x_5631_);
                    v___x_5633_ = v___x_5629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5634_, 0, v___x_5631_);
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
                    v_reuseFailAlloc_5642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5642_, 0, v_a_5636_);
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
                    v_reuseFailAlloc_5650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5650_, 0, v_a_5644_);
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
                    v_reuseFailAlloc_5658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_a_5652_);
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
    mut v___x_5660_: *mut LeanObject,
    mut v_recArgInfo_5661_: *mut LeanObject,
    mut v_fst_5662_: *mut LeanObject,
    mut v_recArgInfos_5663_: *mut LeanObject,
    mut v_positions_5664_: *mut LeanObject,
    mut v_params_5665_: *mut LeanObject,
    mut v_value_5666_: *mut LeanObject,
    mut v_snd_5667_: *mut LeanObject,
    mut v_below_5668_: *mut LeanObject,
    mut v_x_5669_: *mut LeanObject,
    mut v___y_5670_: *mut LeanObject,
    mut v___y_5671_: *mut LeanObject,
    mut v___y_5672_: *mut LeanObject,
    mut v___y_5673_: *mut LeanObject,
    mut v___y_5674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5675_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5673_);
    lean_dec_ref(v___y_5672_);
    lean_dec(v___y_5671_);
    lean_dec_ref(v___y_5670_);
    lean_dec_ref(v_x_5669_);
    lean_dec_ref(v_below_5668_);
    lean_dec_ref(v_snd_5667_);
    lean_dec_ref(v___x_5660_);
    return v_res_5675_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1(
    mut v_recArgInfo_5678_: *mut LeanObject,
    mut v_FType_5679_: *mut LeanObject,
    mut v___x_5680_: *mut LeanObject,
    mut v_recArgInfos_5681_: *mut LeanObject,
    mut v_positions_5682_: *mut LeanObject,
    mut v_params_5683_: *mut LeanObject,
    mut v_xs_5684_: *mut LeanObject,
    mut v_value_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
    mut v___y_5689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: u8 = 0;
    let mut v___x_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5703_: u8 = 0;
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_recArgInfo_5678_);
                v___x_5691_ = l_Lean_Elab_Structural_RecArgInfo_pickIndicesMajor(
                    v_recArgInfo_5678_,
                    v_xs_5684_,
                );
                v_fst_5692_ = lean_ctor_get(v___x_5691_, 0);
                lean_inc(v_fst_5692_);
                v_snd_5693_ = lean_ctor_get(v___x_5691_, 1);
                lean_inc(v_snd_5693_);
                lean_dec_ref(v___x_5691_);
                v___x_5694_ = l_Lean_Meta_instantiateForall(
                    v_FType_5679_,
                    v_fst_5692_,
                    v___y_5686_,
                    v___y_5687_,
                    v___y_5688_,
                    v___y_5689_,
                );
                if lean_obj_tag(v___x_5694_) == 0 {
                    v_a_5695_ = lean_ctor_get(v___x_5694_, 0);
                    lean_inc(v_a_5695_);
                    lean_dec_ref_known(v___x_5694_, 1);
                    v___f_5696_ = lean_alloc_closure(
                        l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__0___boxed
                            as *mut core::ffi::c_void,
                        15,
                        8,
                    );
                    lean_closure_set(v___f_5696_, 0, v___x_5680_);
                    lean_closure_set(v___f_5696_, 1, v_recArgInfo_5678_);
                    lean_closure_set(v___f_5696_, 2, v_fst_5692_);
                    lean_closure_set(v___f_5696_, 3, v_recArgInfos_5681_);
                    lean_closure_set(v___f_5696_, 4, v_positions_5682_);
                    lean_closure_set(v___f_5696_, 5, v_params_5683_);
                    lean_closure_set(v___f_5696_, 6, v_value_5685_);
                    lean_closure_set(v___f_5696_, 7, v_snd_5693_);
                    v___x_5697_ = l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___closed__0;
                    v___x_5698_ = 0;
                    v___x_5699_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_Structural_mkIndPredBRecOnF_spec__1___redArg(v_a_5695_, v___x_5697_, v___f_5696_, v___x_5698_, v___x_5698_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
                    return v___x_5699_;
                } else {
                    lean_dec(v_snd_5693_);
                    lean_dec(v_fst_5692_);
                    lean_dec_ref(v_value_5685_);
                    lean_dec_ref(v_params_5683_);
                    lean_dec_ref(v_positions_5682_);
                    lean_dec_ref(v_recArgInfos_5681_);
                    lean_dec_ref(v___x_5680_);
                    lean_dec_ref(v_recArgInfo_5678_);
                    v_a_5700_ = lean_ctor_get(v___x_5694_, 0);
                    v_isSharedCheck_5707_ = (!lean_is_exclusive(v___x_5694_)) as u8;
                    if v_isSharedCheck_5707_ == 0 {
                        v___x_5702_ = v___x_5694_;
                        v_isShared_5703_ = v_isSharedCheck_5707_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5700_);
                        lean_dec(v___x_5694_);
                        v___x_5702_ = lean_box(0);
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
                    v_reuseFailAlloc_5706_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5706_, 0, v_a_5700_);
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
    mut v_recArgInfo_5708_: *mut LeanObject,
    mut v_FType_5709_: *mut LeanObject,
    mut v___x_5710_: *mut LeanObject,
    mut v_recArgInfos_5711_: *mut LeanObject,
    mut v_positions_5712_: *mut LeanObject,
    mut v_params_5713_: *mut LeanObject,
    mut v_xs_5714_: *mut LeanObject,
    mut v_value_5715_: *mut LeanObject,
    mut v___y_5716_: *mut LeanObject,
    mut v___y_5717_: *mut LeanObject,
    mut v___y_5718_: *mut LeanObject,
    mut v___y_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5721_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5719_);
    lean_dec_ref(v___y_5718_);
    lean_dec(v___y_5717_);
    lean_dec_ref(v___y_5716_);
    return v_res_5721_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF(
    mut v_recArgInfos_5722_: *mut LeanObject,
    mut v_positions_5723_: *mut LeanObject,
    mut v_recArgInfo_5724_: *mut LeanObject,
    mut v_value_5725_: *mut LeanObject,
    mut v_FType_5726_: *mut LeanObject,
    mut v_params_5727_: *mut LeanObject,
    mut v_a_5728_: *mut LeanObject,
    mut v_a_5729_: *mut LeanObject,
    mut v_a_5730_: *mut LeanObject,
    mut v_a_5731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u8 = 0;
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    v___x_5733_ = l_Lean_instInhabitedExpr;
    v___f_5734_ = lean_alloc_closure(
        l_Lean_Elab_Structural_mkIndPredBRecOnF___lam__1___boxed as *mut core::ffi::c_void,
        13,
        6,
    );
    lean_closure_set(v___f_5734_, 0, v_recArgInfo_5724_);
    lean_closure_set(v___f_5734_, 1, v_FType_5726_);
    lean_closure_set(v___f_5734_, 2, v___x_5733_);
    lean_closure_set(v___f_5734_, 3, v_recArgInfos_5722_);
    lean_closure_set(v___f_5734_, 4, v_positions_5723_);
    lean_closure_set(v___f_5734_, 5, v_params_5727_);
    v___x_5735_ = 0;
    v___x_5736_ = l_Lean_Meta_lambdaTelescope___at___00__private_Lean_Elab_PreDefinition_Structural_IndPred_0__Lean_Elab_Structural_withFunTypes_go_spec__1___redArg(v_value_5725_, v___f_5734_, v___x_5735_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_);
    return v___x_5736_;
}
pub unsafe fn l_Lean_Elab_Structural_mkIndPredBRecOnF___boxed(
    mut v_recArgInfos_5737_: *mut LeanObject,
    mut v_positions_5738_: *mut LeanObject,
    mut v_recArgInfo_5739_: *mut LeanObject,
    mut v_value_5740_: *mut LeanObject,
    mut v_FType_5741_: *mut LeanObject,
    mut v_params_5742_: *mut LeanObject,
    mut v_a_5743_: *mut LeanObject,
    mut v_a_5744_: *mut LeanObject,
    mut v_a_5745_: *mut LeanObject,
    mut v_a_5746_: *mut LeanObject,
    mut v_a_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5748_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5746_);
    lean_dec_ref(v_a_5745_);
    lean_dec(v_a_5744_);
    lean_dec_ref(v_a_5743_);
    return v_res_5748_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_HasConstCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IndPredBelow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_IndPred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_IndPred(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_HasConstCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_IndPredBelow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_IndPred(builtin);
}
