// Lean compiler output
// Module: Lean.Elab.Tactic.Decide
// Imports: Lean.Elab.Tactic.Basic Lean.Meta.Tactic.Cleanup Lean.Meta.Native Lean.Elab.Tactic.ElabTerm Lean.Elab.ConfigEval
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Syntax_getArg, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Elab_async, l_Lean_Exception_isRuntime, l_Lean_diagnostics,
    l_Lean_isDiagnosticsEnabled___redArg,
};
use crate::r#gen::Lean::Data::Name::{
    l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf, l_Lean_Name_lt,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::ConfigEval::Basic::{
    l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo,
    l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo, l_Lean_Elab_ConfigEval_ConfigItem_getRootStr,
    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous, l_Lean_Elab_ConfigEval_ConfigItem_shift,
    l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg,
    l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg,
    l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg,
};
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalConfigItem::l_Lean_Elab_ConfigEval_evalBoolItem;
use crate::r#gen::Lean::Elab::ConfigEval::DeriveEvalExpr::l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg;
use crate::r#gen::Lean::Elab::ConfigEval::Instances::l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr;
use crate::r#gen::Lean::Elab::ConfigEval::Types::l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
use crate::r#gen::Lean::Elab::ConfigEval::{
    initialize_Lean_Elab_ConfigEval, runtime_initialize_Lean_Elab_ConfigEval,
};
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTermExceptionId, l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::SyntheticMVars::l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp;
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_SavedState_restore___redArg,
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_saveState___redArg, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg, runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_closeMainGoalUsing,
    runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType___boxed, l_Lean_Elab_Term_getLevelNames___redArg,
    l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData,
    l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_const___override, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOf,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Level::{l_Lean_Level_param___override, l_Lean_mkLevelParam};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_getFVarIds;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_andList, l_Lean_MessageData_hint_x27, l_Lean_MessageData_nil,
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{l_Lean_Meta_mkDecide, l_Lean_Meta_mkDecideProof};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_MVarId_getDecl, l_Lean_MessageData_ofLazyM, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isClass_x3f, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_Extension_getMatcherInfo_x3f, l_Lean_Meta_Match_MatcherInfo_arity,
};
use crate::r#gen::Lean::Meta::Native::{
    initialize_Lean_Meta_Native, l_Lean_Meta_nativeEqTrue, runtime_initialize_Lean_Meta_Native,
};
use crate::r#gen::Lean::Meta::Tactic::AuxLemma::l_Lean_Meta_mkAuxLemma;
use crate::r#gen::Lean::Meta::Tactic::Cleanup::{
    initialize_Lean_Meta_Tactic_Cleanup,
    l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore,
    runtime_initialize_Lean_Meta_Tactic_Cleanup,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::l_Lean_MVarId_revert;
use crate::r#gen::Lean::Meta::Transform::l_Lean_Meta_zetaReduce;
use crate::r#gen::Lean::Meta::TransparencyMode::l_Lean_Meta_TransparencyMode_lt;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::l_Lean_MessageData_ofConst;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::CollectLevelParams::l_Lean_collectLevelParams;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Sorry::{l_Lean_Expr_hasSorry, l_Lean_Expr_hasSyntheticSorry};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_uget_borrowed, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3,
    lean_apply_5, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0_value: LeanStringObject<46> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2_value: LeanStringObject<77> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 77, m_capacity: 77, m_length: 76, m_data: [85, 115, 101, 32, 116, 104, 101, 32, 96, 43, 114, 101, 118, 101, 114, 116, 96, 32, 111, 112, 116, 105, 111, 110, 32, 116, 111, 32, 97, 117, 116, 111, 109, 97, 116, 105, 99, 97, 108, 108, 121, 32, 99, 108, 101, 97, 110, 32, 117, 112, 32, 97, 110, 100, 32, 114, 101, 118, 101, 114, 116, 32, 102, 114, 101, 101, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [69, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 109, 117, 115, 116, 32, 110, 111, 116, 32, 99, 111, 110, 116, 97, 105, 110, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value) as *mut LeanObject,4342836574150310743 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2_value) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 115, 84, 114, 117, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value) as *mut LeanObject,4342836574150310743 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__4_value) as *mut LeanObject,83052734847462153 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 115, 70, 97, 108, 115, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6_value) as *mut LeanObject;
static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value) as *mut LeanObject,4342836574150310743 as *mut LeanObject] };
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__6_value) as *mut LeanObject,14734865452941588245 as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 101, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__0_value) as *mut LeanObject,4342836574150310743 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value) as *mut LeanObject,10995968517338862238 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 18,
        m_capacity: 18,
        m_length: 17,
        m_data: [
            111, 102, 95, 100, 101, 99, 105, 100, 101, 95, 101, 113, 95, 116, 114, 117, 101, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__0_value)
                as *mut LeanObject,
            1819210885479960519 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [84, 97, 99, 116, 105, 99, 32, 96, 0],
    };
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5_value: LeanStringObject<33> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            96, 32, 101, 118, 97, 108, 117, 97, 116, 101, 100, 32, 116, 104, 97, 116, 32, 116, 104,
            101, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [10, 105, 115, 32, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [96, 32, 102, 97, 105, 108, 101, 100, 32, 102, 111, 114, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [10, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 115, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [10, 100, 105, 100, 32, 110, 111, 116, 32, 114, 101, 100, 117, 99, 101, 32, 116, 111, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [96, 32, 111, 114, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [96, 46, 10, 10, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__13_value) as *mut LeanObject,16122875713692181903 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__0_value) as *mut LeanObject,5414616380488487254 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [67, 108, 97, 115, 115, 105, 99, 97, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value) as *mut LeanObject,10854111772627758120 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__16_value) as *mut LeanObject,4033926476496303692 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [82, 101, 100, 117, 99, 116, 105, 111, 110, 32, 103, 111, 116, 32, 115, 116, 117, 99, 107, 32, 111, 110, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20_value: LeanStringObject<28> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 44, 32, 119, 104, 105, 99, 104, 32, 105, 110, 100, 105, 99, 97, 116, 101, 115, 32, 116, 104, 97, 116, 32, 97, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22_value: LeanStringObject<126> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 117, 115, 105, 110, 103, 32, 99, 108, 97, 115, 115, 105, 99, 97, 108, 32, 114, 101, 97, 115, 111, 110, 105, 110, 103, 44, 32, 112, 114, 111, 118, 105, 110, 103, 32, 97, 110, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 101, 120, 105, 115, 116, 115, 32, 114, 97, 116, 104, 101, 114, 32, 116, 104, 97, 110, 32, 103, 105, 118, 105, 110, 103, 32, 97, 32, 99, 111, 110, 99, 114, 101, 116, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 105, 111, 110, 46, 32, 84, 104, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24_value: LeanStringObject<202> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 202, m_capacity: 202, m_length: 201, m_data: [96, 32, 116, 97, 99, 116, 105, 99, 32, 119, 111, 114, 107, 115, 32, 98, 121, 32, 101, 118, 97, 108, 117, 97, 116, 105, 110, 103, 32, 97, 32, 100, 101, 99, 105, 115, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 32, 118, 105, 97, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 44, 32, 97, 110, 100, 32, 105, 116, 32, 99, 97, 110, 110, 111, 116, 32, 109, 97, 107, 101, 32, 112, 114, 111, 103, 114, 101, 115, 115, 32, 119, 105, 116, 104, 32, 115, 117, 99, 104, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 46, 32, 84, 104, 105, 115, 32, 99, 97, 110, 32, 111, 99, 99, 117, 114, 32, 100, 117, 101, 32, 116, 111, 32, 116, 104, 101, 32, 96, 111, 112, 101, 110, 32, 115, 99, 111, 112, 101, 100, 32, 67, 108, 97, 115, 115, 105, 99, 97, 108, 96, 32, 99, 111, 109, 109, 97, 110, 100, 44, 32, 119, 104, 105, 99, 104, 32, 101, 110, 97, 98, 108, 101, 115, 32, 116, 104, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 111, 112, 68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__15_value) as *mut LeanObject,10854111772627758120 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__26_value) as *mut LeanObject,4643704380461739942 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 28, m_data: [82, 101, 100, 117, 99, 116, 105, 111, 110, 32, 103, 111, 116, 32, 115, 116, 117, 99, 107, 32, 111, 110, 32, 96, 226, 150, 184, 96, 32, 40, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [41, 44, 32, 119, 104, 105, 99, 104, 32, 115, 117, 103, 103, 101, 115, 116, 115, 32, 116, 104, 97, 116, 32, 111, 110, 101, 32, 111, 102, 32, 116, 104, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32_value: LeanStringObject<111> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 111, m_capacity: 111, m_length: 110, m_data: [96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 115, 32, 105, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 117, 115, 105, 110, 103, 32, 116, 97, 99, 116, 105, 99, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 114, 119, 96, 32, 111, 114, 32, 96, 115, 105, 109, 112, 96, 46, 32, 84, 111, 32, 97, 118, 111, 105, 100, 32, 116, 97, 99, 116, 105, 99, 115, 44, 32, 109, 97, 107, 101, 32, 117, 115, 101, 32, 111, 102, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [105, 110, 102, 101, 114, 73, 110, 115, 116, 97, 110, 99, 101, 65, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__34_value) as *mut LeanObject,3449385374309517176 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [100, 101, 99, 105, 100, 97, 98, 108, 101, 95, 111, 102, 95, 100, 101, 99, 105, 100, 97, 98, 108, 101, 95, 111, 102, 95, 105, 102, 102, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__36_value) as *mut LeanObject,12216739591175544255 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [96, 32, 116, 111, 32, 97, 108, 116, 101, 114, 32, 97, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [65, 102, 116, 101, 114, 32, 117, 110, 102, 111, 108, 100, 105, 110, 103, 32, 116, 104, 101, 32, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [44, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 103, 111, 116, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 116, 104, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [82, 101, 100, 117, 99, 116, 105, 111, 110, 32, 103, 111, 116, 32, 115, 116, 117, 99, 107, 32, 97, 116, 32, 116, 104, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [96, 32, 112, 114, 111, 118, 101, 100, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 112, 114, 111, 112, 111, 115, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0_value: LeanStringObject<49> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 49, m_capacity: 49, m_length: 48, m_data: [96, 32, 102, 97, 105, 108, 101, 100, 46, 32, 84, 104, 101, 32, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 32, 105, 115, 32, 97, 98, 108, 101, 32, 116, 111, 32, 114, 101, 100, 117, 99, 101, 32, 116, 104, 101, 32, 96, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 44, 32, 98, 117, 116, 32, 116, 104, 101, 32, 107, 101, 114, 110, 101, 108, 32, 102, 97, 105, 108, 115, 32, 119, 105, 116, 104, 58, 10, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0_value: LeanStringObject<65> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 65,
        m_capacity: 65,
        m_length: 64,
        m_data: [
            96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 67, 97, 110, 110, 111, 116, 32, 115, 105,
            109, 117, 108, 116, 97, 110, 101, 111, 117, 115, 108, 121, 32, 115, 101, 116, 32, 98,
            111, 116, 104, 32, 96, 43, 107, 101, 114, 110, 101, 108, 96, 32, 97, 110, 100, 32, 96,
            43, 110, 97, 116, 105, 118, 101, 96, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [68, 101, 99, 105, 100, 101, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value) as *mut LeanObject,14328019226271455753 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 96, 115, 111, 114, 114, 121, 96, 58, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [107, 101, 114, 110, 101, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 105, 118, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 118, 101, 114, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [122, 101, 116, 97, 82, 101, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value) as *mut LeanObject,14328019226271455753 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5_value) as *mut LeanObject,13008991383102940852 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value) as *mut LeanObject,14328019226271455753 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject,2864812835325369166 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value) as *mut LeanObject,14328019226271455753 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject,10630983416307463786 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__4_value) as *mut LeanObject,14328019226271455753 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject,11835302174342499316 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 9,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDecide___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [65536 as *mut LeanObject],
};
static mut l_Lean_Elab_Tactic_evalDecide___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDecide___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDecide___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [100, 101, 99, 105, 100, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalDecide___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDecide___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalDecide___closed__2_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDecide___closed__1_value) as *mut LeanObject,
        10759351130620427500 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_evalDecide___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDecide___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalDecide___closed__1_value) as *mut LeanObject,14249328086033210933 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__2_value) as *mut LeanObject,17394012501637144524 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 373 as usize) << 1) | 1) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 397 as usize) << 1) | 1) as *mut LeanObject,((( 74 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__0_value) as *mut LeanObject,((( 44 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__1_value) as *mut LeanObject,((( 74 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 373 as usize) << 1) | 1) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 373 as usize) << 1) | 1) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__3_value) as *mut LeanObject,((( 48 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__4_value) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            110, 97, 116, 105, 118, 101, 95, 100, 101, 99, 105, 100, 101, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalNativeDecide___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalNativeDecide___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalNativeDecide___closed__0_value)
                as *mut LeanObject,
            9218137442065278391 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalNativeDecide___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalNativeDecide___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [110, 97, 116, 105, 118, 101, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__0_value) as *mut LeanObject,7435882897071006998 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [101, 118, 97, 108, 78, 97, 116, 105, 118, 101, 68, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__1_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__3_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__2_value) as *mut LeanObject,13850857063135086007 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 410 as usize) << 1) | 1) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 417 as usize) << 1) | 1) as *mut LeanObject,((( 160 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__0_value) as *mut LeanObject,((( 50 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__1_value) as *mut LeanObject,((( 160 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 410 as usize) << 1) | 1) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 410 as usize) << 1) | 1) as *mut LeanObject,((( 70 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__3_value) as *mut LeanObject,((( 54 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__4_value) as *mut LeanObject,((( 70 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(
    mut v_e_3720_: *mut LeanObject,
    mut v___y_3721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3743_: u8 = 0;
    let mut v_unused_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3723_ = l_Lean_Expr_hasMVar(v_e_3720_);
                if v___x_3723_ == 0 {
                    v___x_3724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3724_, 0, v_e_3720_);
                    return v___x_3724_;
                } else {
                    v___x_3725_ = lean_st_ref_get(v___y_3721_);
                    v_mctx_3726_ = lean_ctor_get(v___x_3725_, 0);
                    lean_inc_ref(v_mctx_3726_);
                    lean_dec(v___x_3725_);
                    v___x_3727_ = l_Lean_instantiateMVarsCore(v_mctx_3726_, v_e_3720_);
                    v_fst_3728_ = lean_ctor_get(v___x_3727_, 0);
                    lean_inc(v_fst_3728_);
                    v_snd_3729_ = lean_ctor_get(v___x_3727_, 1);
                    lean_inc(v_snd_3729_);
                    lean_dec_ref(v___x_3727_);
                    v___x_3730_ = lean_st_ref_take(v___y_3721_);
                    v_cache_3731_ = lean_ctor_get(v___x_3730_, 1);
                    v_zetaDeltaFVarIds_3732_ = lean_ctor_get(v___x_3730_, 2);
                    v_postponed_3733_ = lean_ctor_get(v___x_3730_, 3);
                    v_diag_3734_ = lean_ctor_get(v___x_3730_, 4);
                    v_isSharedCheck_3743_ = (!lean_is_exclusive(v___x_3730_)) as u8;
                    if v_isSharedCheck_3743_ == 0 {
                        v_unused_3744_ = lean_ctor_get(v___x_3730_, 0);
                        lean_dec(v_unused_3744_);
                        v___x_3736_ = v___x_3730_;
                        v_isShared_3737_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3734_);
                        lean_inc(v_postponed_3733_);
                        lean_inc(v_zetaDeltaFVarIds_3732_);
                        lean_inc(v_cache_3731_);
                        lean_dec(v___x_3730_);
                        v___x_3736_ = lean_box(0);
                        v_isShared_3737_ = v_isSharedCheck_3743_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3737_ == 0 {
                    lean_ctor_set(v___x_3736_, 0, v_snd_3729_);
                    v___x_3739_ = v___x_3736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_snd_3729_);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 1, v_cache_3731_);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 2, v_zetaDeltaFVarIds_3732_);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 3, v_postponed_3733_);
                    lean_ctor_set(v_reuseFailAlloc_3742_, 4, v_diag_3734_);
                    v___x_3739_ = v_reuseFailAlloc_3742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3740_ = lean_st_ref_set(v___y_3721_, v___x_3739_);
                v___x_3741_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3741_, 0, v_fst_3728_);
                return v___x_3741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg___boxed(
    mut v_e_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3748_: *mut LeanObject = core::ptr::null_mut();
    v_res_3748_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_e_3745_, v___y_3746_);
    lean_dec(v___y_3746_);
    return v_res_3748_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1(
    mut v_e_3749_: *mut LeanObject,
    mut v___y_3750_: *mut LeanObject,
    mut v___y_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v___y_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    v___x_3757_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_e_3749_, v___y_3753_);
    return v___x_3757_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___boxed(
    mut v_e_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
    mut v___y_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
    mut v___y_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3766_: *mut LeanObject = core::ptr::null_mut();
    v_res_3766_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1(v_e_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_);
    lean_dec(v___y_3764_);
    lean_dec_ref(v___y_3763_);
    lean_dec(v___y_3762_);
    lean_dec_ref(v___y_3761_);
    lean_dec(v___y_3760_);
    lean_dec_ref(v___y_3759_);
    return v_res_3766_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    v___x_3767_ = lean_box(1);
    v___x_3768_ = l_Lean_MessageData_ofFormat(v___x_3767_);
    return v___x_3768_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    v___x_3772_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__2;
    v___x_3773_ = l_Lean_MessageData_ofFormat(v___x_3772_);
    return v___x_3773_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4(
    mut v_x_3774_: *mut LeanObject,
    mut v_x_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v_before_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3784_: u8 = 0;
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3797_: u8 = 0;
    let mut v_unused_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3775_) == 0 {
                    return v_x_3774_;
                } else {
                    v_head_3776_ = lean_ctor_get(v_x_3775_, 0);
                    v_tail_3777_ = lean_ctor_get(v_x_3775_, 1);
                    v_isSharedCheck_3799_ = (!lean_is_exclusive(v_x_3775_)) as u8;
                    if v_isSharedCheck_3799_ == 0 {
                        v___x_3779_ = v_x_3775_;
                        v_isShared_3780_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3777_);
                        lean_inc(v_head_3776_);
                        lean_dec(v_x_3775_);
                        v___x_3779_ = lean_box(0);
                        v_isShared_3780_ = v_isSharedCheck_3799_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3781_ = lean_ctor_get(v_head_3776_, 0);
                v_isSharedCheck_3797_ = (!lean_is_exclusive(v_head_3776_)) as u8;
                if v_isSharedCheck_3797_ == 0 {
                    v_unused_3798_ = lean_ctor_get(v_head_3776_, 1);
                    lean_dec(v_unused_3798_);
                    v___x_3783_ = v_head_3776_;
                    v_isShared_3784_ = v_isSharedCheck_3797_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_3781_);
                    lean_dec(v_head_3776_);
                    v___x_3783_ = lean_box(0);
                    v_isShared_3784_ = v_isSharedCheck_3797_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3785_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0);
                if v_isShared_3784_ == 0 {
                    lean_ctor_set_tag(v___x_3783_, 7);
                    lean_ctor_set(v___x_3783_, 1, v___x_3785_);
                    lean_ctor_set(v___x_3783_, 0, v_x_3774_);
                    v___x_3787_ = v___x_3783_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3796_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_x_3774_);
                    lean_ctor_set(v_reuseFailAlloc_3796_, 1, v___x_3785_);
                    v___x_3787_ = v_reuseFailAlloc_3796_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3788_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__3);
                if v_isShared_3780_ == 0 {
                    lean_ctor_set_tag(v___x_3779_, 7);
                    lean_ctor_set(v___x_3779_, 1, v___x_3788_);
                    lean_ctor_set(v___x_3779_, 0, v___x_3787_);
                    v___x_3790_ = v___x_3779_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3787_);
                    lean_ctor_set(v_reuseFailAlloc_3795_, 1, v___x_3788_);
                    v___x_3790_ = v_reuseFailAlloc_3795_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3791_ = l_Lean_MessageData_ofSyntax(v_before_3781_);
                v___x_3792_ = l_Lean_indentD(v___x_3791_);
                v___x_3793_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3793_, 0, v___x_3790_);
                lean_ctor_set(v___x_3793_, 1, v___x_3792_);
                v_x_3774_ = v___x_3793_;
                v_x_3775_ = v_tail_3777_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(
    mut v_opts_3800_: *mut LeanObject,
    mut v_opt_3801_: *mut LeanObject,
) -> u8 {
    let mut v_name_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    v_name_3802_ = lean_ctor_get(v_opt_3801_, 0);
    v_defValue_3803_ = lean_ctor_get(v_opt_3801_, 1);
    v_map_3804_ = lean_ctor_get(v_opts_3800_, 0);
    v___x_3805_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3804_,
            v_name_3802_,
        );
    if lean_obj_tag(v___x_3805_) == 0 {
        let mut v___x_3806_: u8 = 0;
        v___x_3806_ = (lean_unbox(v_defValue_3803_) as u8);
        return v___x_3806_;
    } else {
        let mut v_val_3807_: *mut LeanObject = core::ptr::null_mut();
        v_val_3807_ = lean_ctor_get(v___x_3805_, 0);
        lean_inc(v_val_3807_);
        lean_dec_ref_known(v___x_3805_, 1);
        if lean_obj_tag(v_val_3807_) == 1 {
            let mut v_v_3808_: u8 = 0;
            v_v_3808_ = lean_ctor_get_uint8(v_val_3807_, 0 as u32);
            lean_dec_ref_known(v_val_3807_, 0);
            return v_v_3808_;
        } else {
            let mut v___x_3809_: u8 = 0;
            lean_dec(v_val_3807_);
            v___x_3809_ = (lean_unbox(v_defValue_3803_) as u8);
            return v___x_3809_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3___boxed(
    mut v_opts_3810_: *mut LeanObject,
    mut v_opt_3811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3812_: u8 = 0;
    let mut v_r_3813_: *mut LeanObject = core::ptr::null_mut();
    v_res_3812_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v_opts_3810_, v_opt_3811_);
    lean_dec_ref(v_opt_3811_);
    lean_dec_ref(v_opts_3810_);
    v_r_3813_ = lean_box((v_res_3812_) as usize);
    return v_r_3813_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__1;
    v___x_3818_ = l_Lean_MessageData_ofFormat(v___x_3817_);
    return v___x_3818_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(
    mut v_msgData_3819_: *mut LeanObject,
    mut v_macroStack_3820_: *mut LeanObject,
    mut v___y_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3832_: u8 = 0;
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v_unused_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3823_ = lean_ctor_get(v___y_3821_, 2);
                v___x_3824_ = l_Lean_Elab_pp_macroStack;
                v___x_3825_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v_options_3823_, v___x_3824_);
                if v___x_3825_ == 0 {
                    lean_dec(v_macroStack_3820_);
                    v___x_3826_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3826_, 0, v_msgData_3819_);
                    return v___x_3826_;
                } else {
                    if lean_obj_tag(v_macroStack_3820_) == 0 {
                        v___x_3827_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3827_, 0, v_msgData_3819_);
                        return v___x_3827_;
                    } else {
                        v_head_3828_ = lean_ctor_get(v_macroStack_3820_, 0);
                        lean_inc(v_head_3828_);
                        v_after_3829_ = lean_ctor_get(v_head_3828_, 1);
                        v_isSharedCheck_3844_ = (!lean_is_exclusive(v_head_3828_)) as u8;
                        if v_isSharedCheck_3844_ == 0 {
                            v_unused_3845_ = lean_ctor_get(v_head_3828_, 0);
                            lean_dec(v_unused_3845_);
                            v___x_3831_ = v_head_3828_;
                            v_isShared_3832_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_3829_);
                            lean_dec(v_head_3828_);
                            v___x_3831_ = lean_box(0);
                            v_isShared_3832_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3833_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4___closed__0);
                if v_isShared_3832_ == 0 {
                    lean_ctor_set_tag(v___x_3831_, 7);
                    lean_ctor_set(v___x_3831_, 1, v___x_3833_);
                    lean_ctor_set(v___x_3831_, 0, v_msgData_3819_);
                    v___x_3835_ = v___x_3831_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_msgData_3819_);
                    lean_ctor_set(v_reuseFailAlloc_3843_, 1, v___x_3833_);
                    v___x_3835_ = v_reuseFailAlloc_3843_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3836_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___closed__2);
                v___x_3837_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3837_, 0, v___x_3835_);
                lean_ctor_set(v___x_3837_, 1, v___x_3836_);
                v___x_3838_ = l_Lean_MessageData_ofSyntax(v_after_3829_);
                v___x_3839_ = l_Lean_indentD(v___x_3838_);
                v_msgData_3840_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_3840_, 0, v___x_3837_);
                lean_ctor_set(v_msgData_3840_, 1, v___x_3839_);
                v___x_3841_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__4(v_msgData_3840_, v_macroStack_3820_);
                v___x_3842_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3842_, 0, v___x_3841_);
                return v___x_3842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg___boxed(
    mut v_msgData_3846_: *mut LeanObject,
    mut v_macroStack_3847_: *mut LeanObject,
    mut v___y_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3850_: *mut LeanObject = core::ptr::null_mut();
    v_res_3850_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_msgData_3846_, v_macroStack_3847_, v___y_3848_);
    lean_dec_ref(v___y_3848_);
    return v_res_3850_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(
    mut v_msgData_3851_: *mut LeanObject,
    mut v___y_3852_: *mut LeanObject,
    mut v___y_3853_: *mut LeanObject,
    mut v___y_3854_: *mut LeanObject,
    mut v___y_3855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    v___x_3857_ = lean_st_ref_get(v___y_3855_);
    v_env_3858_ = lean_ctor_get(v___x_3857_, 0);
    lean_inc_ref(v_env_3858_);
    lean_dec(v___x_3857_);
    v___x_3859_ = lean_st_ref_get(v___y_3853_);
    v_mctx_3860_ = lean_ctor_get(v___x_3859_, 0);
    lean_inc_ref(v_mctx_3860_);
    lean_dec(v___x_3859_);
    v_lctx_3861_ = lean_ctor_get(v___y_3852_, 2);
    v_options_3862_ = lean_ctor_get(v___y_3854_, 2);
    lean_inc_ref(v_options_3862_);
    lean_inc_ref(v_lctx_3861_);
    v___x_3863_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3863_, 0, v_env_3858_);
    lean_ctor_set(v___x_3863_, 1, v_mctx_3860_);
    lean_ctor_set(v___x_3863_, 2, v_lctx_3861_);
    lean_ctor_set(v___x_3863_, 3, v_options_3862_);
    v___x_3864_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3864_, 0, v___x_3863_);
    lean_ctor_set(v___x_3864_, 1, v_msgData_3851_);
    v___x_3865_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3865_, 0, v___x_3864_);
    return v___x_3865_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0___boxed(
    mut v_msgData_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3872_: *mut LeanObject = core::ptr::null_mut();
    v_res_3872_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msgData_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
    lean_dec(v___y_3870_);
    lean_dec_ref(v___y_3869_);
    lean_dec(v___y_3868_);
    lean_dec_ref(v___y_3867_);
    return v_res_3872_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(
    mut v_msg_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
    mut v___y_3875_: *mut LeanObject,
    mut v___y_3876_: *mut LeanObject,
    mut v___y_3877_: *mut LeanObject,
    mut v___y_3878_: *mut LeanObject,
    mut v___y_3879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3890_: u8 = 0;
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3881_ = lean_ctor_get(v___y_3878_, 5);
                v___x_3882_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_3873_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
                v_a_3883_ = lean_ctor_get(v___x_3882_, 0);
                lean_inc(v_a_3883_);
                lean_dec_ref(v___x_3882_);
                v_macroStack_3884_ = lean_ctor_get(v___y_3874_, 1);
                v___x_3885_ = l_Lean_Elab_getBetterRef(v_ref_3881_, v_macroStack_3884_);
                lean_inc(v_macroStack_3884_);
                v___x_3886_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_a_3883_, v_macroStack_3884_, v___y_3878_);
                v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
                v_isSharedCheck_3895_ = (!lean_is_exclusive(v___x_3886_)) as u8;
                if v_isSharedCheck_3895_ == 0 {
                    v___x_3889_ = v___x_3886_;
                    v_isShared_3890_ = v_isSharedCheck_3895_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3887_);
                    lean_dec(v___x_3886_);
                    v___x_3889_ = lean_box(0);
                    v_isShared_3890_ = v_isSharedCheck_3895_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3891_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3891_, 0, v___x_3885_);
                lean_ctor_set(v___x_3891_, 1, v_a_3887_);
                if v_isShared_3890_ == 0 {
                    lean_ctor_set_tag(v___x_3889_, 1);
                    lean_ctor_set(v___x_3889_, 0, v___x_3891_);
                    v___x_3893_ = v___x_3889_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
                    v___x_3893_ = v_reuseFailAlloc_3894_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3893_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg___boxed(
    mut v_msg_3896_: *mut LeanObject,
    mut v___y_3897_: *mut LeanObject,
    mut v___y_3898_: *mut LeanObject,
    mut v___y_3899_: *mut LeanObject,
    mut v___y_3900_: *mut LeanObject,
    mut v___y_3901_: *mut LeanObject,
    mut v___y_3902_: *mut LeanObject,
    mut v___y_3903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3904_: *mut LeanObject = core::ptr::null_mut();
    v_res_3904_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_3896_, v___y_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_, v___y_3902_);
    lean_dec(v___y_3902_);
    lean_dec_ref(v___y_3901_);
    lean_dec(v___y_3900_);
    lean_dec_ref(v___y_3899_);
    lean_dec(v___y_3898_);
    lean_dec_ref(v___y_3897_);
    return v_res_3904_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1()
-> *mut LeanObject {
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    v___x_3906_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__0;
    v___x_3907_ = l_Lean_stringToMessageData(v___x_3906_);
    return v___x_3907_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3()
-> *mut LeanObject {
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    v___x_3909_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__2;
    v___x_3910_ = l_Lean_stringToMessageData(v___x_3909_);
    return v___x_3910_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4()
-> *mut LeanObject {
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    v___x_3911_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__3);
    v___x_3912_ = l_Lean_MessageData_hint_x27(v___x_3911_);
    return v___x_3912_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6()
-> *mut LeanObject {
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    v___x_3914_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__5;
    v___x_3915_ = l_Lean_stringToMessageData(v___x_3914_);
    return v___x_3915_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(
    mut v_expectedType_3916_: *mut LeanObject,
    mut v_a_3917_: *mut LeanObject,
    mut v_a_3918_: *mut LeanObject,
    mut v_a_3919_: *mut LeanObject,
    mut v_a_3920_: *mut LeanObject,
    mut v_a_3921_: *mut LeanObject,
    mut v_a_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3943_: u8 = 0;
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3947_: u8 = 0;
    let mut v_expectedType_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: u8 = 0;
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: u8 = 0;
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3969_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_expectedType_3916_, v_a_3920_);
                v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
                lean_inc(v_a_3970_);
                lean_dec_ref(v___x_3969_);
                v___x_3971_ = l_Lean_Expr_hasFVar(v_a_3970_);
                if v___x_3971_ == 0 {
                    v_expectedType_3949_ = v_a_3970_;
                    v___y_3950_ = v_a_3917_;
                    v___y_3951_ = v_a_3918_;
                    v___y_3952_ = v_a_3919_;
                    v___y_3953_ = v_a_3920_;
                    v___y_3954_ = v_a_3921_;
                    v___y_3955_ = v_a_3922_;
                    state = 4;
                    continue;
                } else {
                    v___x_3972_ = l_Lean_Meta_zetaReduce(
                        v_a_3970_,
                        v___x_3971_,
                        v___x_3971_,
                        v___x_3971_,
                        v_a_3919_,
                        v_a_3920_,
                        v_a_3921_,
                        v_a_3922_,
                    );
                    if lean_obj_tag(v___x_3972_) == 0 {
                        v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
                        lean_inc(v_a_3973_);
                        lean_dec_ref_known(v___x_3972_, 1);
                        v_expectedType_3949_ = v_a_3973_;
                        v___y_3950_ = v_a_3917_;
                        v___y_3951_ = v_a_3918_;
                        v___y_3952_ = v_a_3919_;
                        v___y_3953_ = v_a_3920_;
                        v___y_3954_ = v_a_3921_;
                        v___y_3955_ = v_a_3922_;
                        state = 4;
                        continue;
                    } else {
                        return v___x_3972_;
                    }
                }
            }
            1 => {
                v___x_3932_ = l_Lean_Expr_hasFVar(v___y_3925_);
                if v___x_3932_ == 0 {
                    v___x_3933_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3933_, 0, v___y_3925_);
                    return v___x_3933_;
                } else {
                    v___x_3934_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__1);
                    v___x_3935_ = l_Lean_indentExpr(v___y_3925_);
                    v___x_3936_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3936_, 0, v___x_3934_);
                    lean_ctor_set(v___x_3936_, 1, v___x_3935_);
                    v___x_3937_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__4);
                    v___x_3938_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3938_, 0, v___x_3936_);
                    lean_ctor_set(v___x_3938_, 1, v___x_3937_);
                    v___x_3939_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3938_, v___y_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
                    v_a_3940_ = lean_ctor_get(v___x_3939_, 0);
                    v_isSharedCheck_3947_ = (!lean_is_exclusive(v___x_3939_)) as u8;
                    if v_isSharedCheck_3947_ == 0 {
                        v___x_3942_ = v___x_3939_;
                        v_isShared_3943_ = v_isSharedCheck_3947_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3940_);
                        lean_dec(v___x_3939_);
                        v___x_3942_ = lean_box(0);
                        v_isShared_3943_ = v_isSharedCheck_3947_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3943_ == 0 {
                    v___x_3945_ = v___x_3942_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3940_);
                    v___x_3945_ = v_reuseFailAlloc_3946_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3945_;
            }
            4 => {
                v___x_3956_ = l_Lean_Expr_hasMVar(v_expectedType_3949_);
                if v___x_3956_ == 0 {
                    v___y_3925_ = v_expectedType_3949_;
                    v___y_3926_ = v___y_3950_;
                    v___y_3927_ = v___y_3951_;
                    v___y_3928_ = v___y_3952_;
                    v___y_3929_ = v___y_3953_;
                    v___y_3930_ = v___y_3954_;
                    v___y_3931_ = v___y_3955_;
                    state = 1;
                    continue;
                } else {
                    v___x_3957_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___closed__6);
                    v___x_3958_ = l_Lean_indentExpr(v_expectedType_3949_);
                    v___x_3959_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3959_, 0, v___x_3957_);
                    lean_ctor_set(v___x_3959_, 1, v___x_3958_);
                    v___x_3960_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_3959_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
                    v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
                    v_isSharedCheck_3968_ = (!lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_3968_ == 0 {
                        v___x_3963_ = v___x_3960_;
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3961_);
                        lean_dec(v___x_3960_);
                        v___x_3963_ = lean_box(0);
                        v_isShared_3964_ = v_isSharedCheck_3968_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3964_ == 0 {
                    v___x_3966_ = v___x_3963_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3966_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide___boxed(
    mut v_expectedType_3974_: *mut LeanObject,
    mut v_a_3975_: *mut LeanObject,
    mut v_a_3976_: *mut LeanObject,
    mut v_a_3977_: *mut LeanObject,
    mut v_a_3978_: *mut LeanObject,
    mut v_a_3979_: *mut LeanObject,
    mut v_a_3980_: *mut LeanObject,
    mut v_a_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3982_: *mut LeanObject = core::ptr::null_mut();
    v_res_3982_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(
        v_expectedType_3974_,
        v_a_3975_,
        v_a_3976_,
        v_a_3977_,
        v_a_3978_,
        v_a_3979_,
        v_a_3980_,
    );
    lean_dec(v_a_3980_);
    lean_dec_ref(v_a_3979_);
    lean_dec(v_a_3978_);
    lean_dec_ref(v_a_3977_);
    lean_dec(v_a_3976_);
    lean_dec_ref(v_a_3975_);
    return v_res_3982_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(
    mut v_00_u03b1_3983_: *mut LeanObject,
    mut v_msg_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3992_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v_msg_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_, v___y_3990_);
    return v___x_3992_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___boxed(
    mut v_00_u03b1_3993_: *mut LeanObject,
    mut v_msg_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
    mut v___y_3999_: *mut LeanObject,
    mut v___y_4000_: *mut LeanObject,
    mut v___y_4001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4002_: *mut LeanObject = core::ptr::null_mut();
    v_res_4002_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0(v_00_u03b1_3993_, v_msg_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
    lean_dec(v___y_4000_);
    lean_dec_ref(v___y_3999_);
    lean_dec(v___y_3998_);
    lean_dec_ref(v___y_3997_);
    lean_dec(v___y_3996_);
    lean_dec_ref(v___y_3995_);
    return v_res_4002_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(
    mut v_msgData_4003_: *mut LeanObject,
    mut v_macroStack_4004_: *mut LeanObject,
    mut v___y_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
    mut v___y_4010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    v___x_4012_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___redArg(v_msgData_4003_, v_macroStack_4004_, v___y_4009_);
    return v___x_4012_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1___boxed(
    mut v_msgData_4013_: *mut LeanObject,
    mut v_macroStack_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
    mut v___y_4016_: *mut LeanObject,
    mut v___y_4017_: *mut LeanObject,
    mut v___y_4018_: *mut LeanObject,
    mut v___y_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4022_: *mut LeanObject = core::ptr::null_mut();
    v_res_4022_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1(v_msgData_4013_, v_macroStack_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
    lean_dec(v___y_4020_);
    lean_dec_ref(v___y_4019_);
    lean_dec(v___y_4018_);
    lean_dec_ref(v___y_4017_);
    lean_dec(v___y_4016_);
    lean_dec_ref(v___y_4015_);
    return v_res_4022_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(
    mut v_declName_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    v___x_4026_ = lean_st_ref_get(v___y_4024_);
    v_env_4027_ = lean_ctor_get(v___x_4026_, 0);
    lean_inc_ref(v_env_4027_);
    lean_dec(v___x_4026_);
    v___x_4028_ = l_Lean_Meta_Match_Extension_getMatcherInfo_x3f(v_env_4027_, v_declName_4023_);
    v___x_4029_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4029_, 0, v___x_4028_);
    return v___x_4029_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg___boxed(
    mut v_declName_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4033_: *mut LeanObject = core::ptr::null_mut();
    v_res_4033_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_4030_, v___y_4031_);
    lean_dec(v___y_4031_);
    return v_res_4033_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(
    mut v_declName_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
    mut v___y_4036_: *mut LeanObject,
    mut v___y_4037_: *mut LeanObject,
    mut v___y_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    v___x_4040_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_4034_, v___y_4038_);
    return v___x_4040_;
}
pub unsafe fn l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___boxed(
    mut v_declName_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4047_: *mut LeanObject = core::ptr::null_mut();
    v_res_4047_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0(v_declName_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
    lean_dec(v___y_4045_);
    lean_dec_ref(v___y_4044_);
    lean_dec(v___y_4043_);
    lean_dec_ref(v___y_4042_);
    return v_res_4047_;
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(
    mut v_x_4048_: *mut LeanObject,
    mut v_x_4049_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4048_) == 0 {
        if lean_obj_tag(v_x_4049_) == 0 {
            let mut v___x_4050_: u8 = 0;
            v___x_4050_ = 1;
            return v___x_4050_;
        } else {
            let mut v___x_4051_: u8 = 0;
            v___x_4051_ = 0;
            return v___x_4051_;
        }
    } else {
        if lean_obj_tag(v_x_4049_) == 0 {
            let mut v___x_4052_: u8 = 0;
            v___x_4052_ = 0;
            return v___x_4052_;
        } else {
            let mut v_val_4053_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_4054_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4055_: u8 = 0;
            v_val_4053_ = lean_ctor_get(v_x_4048_, 0);
            v_val_4054_ = lean_ctor_get(v_x_4049_, 0);
            v___x_4055_ = lean_name_eq(v_val_4053_, v_val_4054_);
            return v___x_4055_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1___boxed(
    mut v_x_4056_: *mut LeanObject,
    mut v_x_4057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4058_: u8 = 0;
    let mut v_r_4059_: *mut LeanObject = core::ptr::null_mut();
    v_res_4058_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_x_4056_, v_x_4057_);
    lean_dec(v_x_4057_);
    lean_dec(v_x_4056_);
    v_r_4059_ = lean_box((v_res_4058_) as usize);
    return v_r_4059_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    v___x_4065_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4066_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4066_, 0, v___x_4065_);
    return v___x_4066_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    v___x_4067_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__3);
    v___x_4068_ = l_Lean_MessageData_ofFormat(v___x_4067_);
    return v___x_4068_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    v___x_4069_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__4);
    v___x_4070_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__2;
    v___x_4071_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_4071_, 0, v___x_4070_);
    lean_ctor_set(v___x_4071_, 1, v___x_4069_);
    return v___x_4071_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(
    mut v_ref_4072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    v___x_4074_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___closed__5);
    v___x_4075_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4075_, 0, v_ref_4072_);
    lean_ctor_set(v___x_4075_, 1, v___x_4074_);
    v___x_4076_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4076_, 0, v___x_4075_);
    return v___x_4076_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg___boxed(
    mut v_ref_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4079_: *mut LeanObject = core::ptr::null_mut();
    v_res_4079_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(v_ref_4077_);
    return v_res_4079_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3(
    mut v_00_u03b1_4080_: *mut LeanObject,
    mut v_ref_4081_: *mut LeanObject,
    mut v___y_4082_: *mut LeanObject,
    mut v___y_4083_: *mut LeanObject,
    mut v___y_4084_: *mut LeanObject,
    mut v___y_4085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    v___x_4087_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(v_ref_4081_);
    return v___x_4087_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___boxed(
    mut v_00_u03b1_4088_: *mut LeanObject,
    mut v_ref_4089_: *mut LeanObject,
    mut v___y_4090_: *mut LeanObject,
    mut v___y_4091_: *mut LeanObject,
    mut v___y_4092_: *mut LeanObject,
    mut v___y_4093_: *mut LeanObject,
    mut v___y_4094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4095_: *mut LeanObject = core::ptr::null_mut();
    v_res_4095_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3(v_00_u03b1_4088_, v_ref_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
    lean_dec(v___y_4093_);
    lean_dec_ref(v___y_4092_);
    lean_dec(v___y_4091_);
    lean_dec_ref(v___y_4090_);
    return v_res_4095_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2()
-> *mut LeanObject {
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4117_: *mut LeanObject = core::ptr::null_mut();
    v___x_4116_ = lean_box(0);
    v_dummy_4117_ = l_Lean_Expr_sort___override(v___x_4116_);
    return v_dummy_4117_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(
    mut v_inst_4118_: *mut LeanObject,
    mut v_a_4119_: *mut LeanObject,
    mut v_a_4120_: *mut LeanObject,
    mut v_a_4121_: *mut LeanObject,
    mut v_a_4122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4136_: u8 = 0;
    let mut v_cancelTk_x3f_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4138_: u8 = 0;
    let mut v_inheritedTraceOptions_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: u8 = 0;
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4155_: u8 = 0;
    let mut v_val_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: u8 = 0;
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4174_: u8 = 0;
    let mut v_fst_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_a_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4191_: u8 = 0;
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4195_: u8 = 0;
    let mut v_a_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4203_: u8 = 0;
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: u8 = 0;
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_4124_ = lean_ctor_get(v_a_4121_, 0);
                lean_inc_ref(v_fileName_4124_);
                v_fileMap_4125_ = lean_ctor_get(v_a_4121_, 1);
                lean_inc_ref(v_fileMap_4125_);
                v_options_4126_ = lean_ctor_get(v_a_4121_, 2);
                lean_inc_ref(v_options_4126_);
                v_currRecDepth_4127_ = lean_ctor_get(v_a_4121_, 3);
                lean_inc(v_currRecDepth_4127_);
                v_maxRecDepth_4128_ = lean_ctor_get(v_a_4121_, 4);
                lean_inc(v_maxRecDepth_4128_);
                v_ref_4129_ = lean_ctor_get(v_a_4121_, 5);
                lean_inc(v_ref_4129_);
                v_currNamespace_4130_ = lean_ctor_get(v_a_4121_, 6);
                lean_inc(v_currNamespace_4130_);
                v_openDecls_4131_ = lean_ctor_get(v_a_4121_, 7);
                lean_inc(v_openDecls_4131_);
                v_initHeartbeats_4132_ = lean_ctor_get(v_a_4121_, 8);
                lean_inc(v_initHeartbeats_4132_);
                v_maxHeartbeats_4133_ = lean_ctor_get(v_a_4121_, 9);
                lean_inc(v_maxHeartbeats_4133_);
                v_quotContext_4134_ = lean_ctor_get(v_a_4121_, 10);
                lean_inc(v_quotContext_4134_);
                v_currMacroScope_4135_ = lean_ctor_get(v_a_4121_, 11);
                lean_inc(v_currMacroScope_4135_);
                v_diag_4136_ = lean_ctor_get_uint8(
                    v_a_4121_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4137_ = lean_ctor_get(v_a_4121_, 12);
                lean_inc(v_cancelTk_x3f_4137_);
                v_suppressElabErrors_4138_ = lean_ctor_get_uint8(
                    v_a_4121_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4139_ = lean_ctor_get(v_a_4121_, 13);
                lean_inc_ref(v_inheritedTraceOptions_4139_);
                lean_dec_ref(v_a_4121_);
                v___x_4206_ = lean_unsigned_to_nat(0);
                v___x_4207_ = lean_nat_dec_eq(v_maxRecDepth_4128_, v___x_4206_);
                if v___x_4207_ == 0 {
                    v___x_4208_ = lean_nat_dec_eq(v_currRecDepth_4127_, v_maxRecDepth_4128_);
                    if v___x_4208_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_inheritedTraceOptions_4139_);
                        lean_dec(v_cancelTk_x3f_4137_);
                        lean_dec(v_currMacroScope_4135_);
                        lean_dec(v_quotContext_4134_);
                        lean_dec(v_maxHeartbeats_4133_);
                        lean_dec(v_initHeartbeats_4132_);
                        lean_dec(v_openDecls_4131_);
                        lean_dec(v_currNamespace_4130_);
                        lean_dec(v_maxRecDepth_4128_);
                        lean_dec(v_currRecDepth_4127_);
                        lean_dec_ref(v_options_4126_);
                        lean_dec_ref(v_fileMap_4125_);
                        lean_dec_ref(v_fileName_4124_);
                        lean_dec_ref(v_inst_4118_);
                        v___x_4209_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__3___redArg(v_ref_4129_);
                        return v___x_4209_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4141_ = lean_unsigned_to_nat(1);
                v___x_4142_ = lean_nat_add(v_currRecDepth_4127_, v___x_4141_);
                lean_dec(v_currRecDepth_4127_);
                v___x_4143_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4143_, 0, v_fileName_4124_);
                lean_ctor_set(v___x_4143_, 1, v_fileMap_4125_);
                lean_ctor_set(v___x_4143_, 2, v_options_4126_);
                lean_ctor_set(v___x_4143_, 3, v___x_4142_);
                lean_ctor_set(v___x_4143_, 4, v_maxRecDepth_4128_);
                lean_ctor_set(v___x_4143_, 5, v_ref_4129_);
                lean_ctor_set(v___x_4143_, 6, v_currNamespace_4130_);
                lean_ctor_set(v___x_4143_, 7, v_openDecls_4131_);
                lean_ctor_set(v___x_4143_, 8, v_initHeartbeats_4132_);
                lean_ctor_set(v___x_4143_, 9, v_maxHeartbeats_4133_);
                lean_ctor_set(v___x_4143_, 10, v_quotContext_4134_);
                lean_ctor_set(v___x_4143_, 11, v_currMacroScope_4135_);
                lean_ctor_set(v___x_4143_, 12, v_cancelTk_x3f_4137_);
                lean_ctor_set(v___x_4143_, 13, v_inheritedTraceOptions_4139_);
                lean_ctor_set_uint8(
                    v___x_4143_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_4136_,
                );
                lean_ctor_set_uint8(
                    v___x_4143_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4138_,
                );
                lean_inc(v_a_4122_);
                lean_inc_ref(v___x_4143_);
                lean_inc(v_a_4120_);
                lean_inc_ref(v_a_4119_);
                v___x_4144_ = lean_whnf(v_inst_4118_, v_a_4119_, v_a_4120_, v___x_4143_, v_a_4122_);
                if lean_obj_tag(v___x_4144_) == 0 {
                    v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
                    lean_inc(v_a_4145_);
                    v___x_4146_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__1;
                    v___x_4147_ = lean_unsigned_to_nat(5);
                    v___x_4148_ = l_Lean_Expr_isAppOfArity(v_a_4145_, v___x_4146_, v___x_4147_);
                    if v___x_4148_ == 0 {
                        v___x_4149_ = l_Lean_Expr_getAppFn(v_a_4145_);
                        if lean_obj_tag(v___x_4149_) == 4 {
                            lean_dec_ref_known(v___x_4144_, 1);
                            v_declName_4150_ = lean_ctor_get(v___x_4149_, 0);
                            lean_inc(v_declName_4150_);
                            lean_dec_ref_known(v___x_4149_, 2);
                            v___x_4151_ = l_Lean_Meta_getMatcherInfo_x3f___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__0___redArg(v_declName_4150_, v_a_4122_);
                            if lean_obj_tag(v___x_4151_) == 0 {
                                v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
                                v_isSharedCheck_4195_ = (!lean_is_exclusive(v___x_4151_)) as u8;
                                if v_isSharedCheck_4195_ == 0 {
                                    v___x_4154_ = v___x_4151_;
                                    v_isShared_4155_ = v_isSharedCheck_4195_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_4152_);
                                    lean_dec(v___x_4151_);
                                    v___x_4154_ = lean_box(0);
                                    v_isShared_4155_ = v_isSharedCheck_4195_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_4145_);
                                lean_dec_ref_known(v___x_4143_, 14);
                                v_a_4196_ = lean_ctor_get(v___x_4151_, 0);
                                v_isSharedCheck_4203_ = (!lean_is_exclusive(v___x_4151_)) as u8;
                                if v_isSharedCheck_4203_ == 0 {
                                    v___x_4198_ = v___x_4151_;
                                    v_isShared_4199_ = v_isSharedCheck_4203_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_4196_);
                                    lean_dec(v___x_4151_);
                                    v___x_4198_ = lean_box(0);
                                    v_isShared_4199_ = v_isSharedCheck_4203_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_4149_);
                            lean_dec(v_a_4145_);
                            lean_dec_ref_known(v___x_4143_, 14);
                            return v___x_4144_;
                        }
                    } else {
                        lean_dec_ref_known(v___x_4144_, 1);
                        v___x_4204_ = l_Lean_Expr_appArg_x21(v_a_4145_);
                        lean_dec(v_a_4145_);
                        v_inst_4118_ = v___x_4204_;
                        v_a_4121_ = v___x_4143_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_4143_, 14);
                    return v___x_4144_;
                }
            }
            2 => {
                if lean_obj_tag(v_a_4152_) == 1 {
                    v_val_4156_ = lean_ctor_get(v_a_4152_, 0);
                    lean_inc(v_val_4156_);
                    lean_dec_ref_known(v_a_4152_, 1);
                    v___x_4157_ = l_Lean_Expr_getAppNumArgs(v_a_4145_);
                    v___x_4158_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_4156_);
                    v___x_4159_ = lean_nat_dec_eq(v___x_4157_, v___x_4158_);
                    if v___x_4159_ == 0 {
                        lean_dec(v___x_4158_);
                        lean_dec(v___x_4157_);
                        lean_dec(v_val_4156_);
                        lean_dec_ref_known(v___x_4143_, 14);
                        if v_isShared_4155_ == 0 {
                            lean_ctor_set(v___x_4154_, 0, v_a_4145_);
                            v___x_4161_ = v___x_4154_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4145_);
                            v___x_4161_ = v_reuseFailAlloc_4162_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4154_);
                        v_numDiscrs_4163_ = lean_ctor_get(v_val_4156_, 1);
                        lean_inc(v_numDiscrs_4163_);
                        v___x_4164_ = lean_unsigned_to_nat(0);
                        v___x_4165_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1;
                        v_dummy_4166_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___closed__2);
                        lean_inc(v___x_4157_);
                        v___x_4167_ = lean_mk_array(v___x_4157_, v_dummy_4166_);
                        v___x_4168_ = lean_nat_sub(v___x_4157_, v___x_4141_);
                        lean_inc(v_a_4145_);
                        v___x_4169_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                            v_a_4145_,
                            v___x_4167_,
                            v___x_4168_,
                        );
                        v___x_4170_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_numDiscrs_4163_, v_val_4156_, v___x_4169_, v___x_4148_, v___x_4157_, v___x_4158_, v___x_4164_, v___x_4165_, v_a_4119_, v_a_4120_, v___x_4143_, v_a_4122_);
                        lean_dec_ref_known(v___x_4143_, 14);
                        lean_dec(v___x_4158_);
                        lean_dec(v___x_4157_);
                        lean_dec_ref(v___x_4169_);
                        lean_dec(v_val_4156_);
                        lean_dec(v_numDiscrs_4163_);
                        if lean_obj_tag(v___x_4170_) == 0 {
                            v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
                            v_isSharedCheck_4183_ = (!lean_is_exclusive(v___x_4170_)) as u8;
                            if v_isSharedCheck_4183_ == 0 {
                                v___x_4173_ = v___x_4170_;
                                v_isShared_4174_ = v_isSharedCheck_4183_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4171_);
                                lean_dec(v___x_4170_);
                                v___x_4173_ = lean_box(0);
                                v_isShared_4174_ = v_isSharedCheck_4183_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4145_);
                            v_a_4184_ = lean_ctor_get(v___x_4170_, 0);
                            v_isSharedCheck_4191_ = (!lean_is_exclusive(v___x_4170_)) as u8;
                            if v_isSharedCheck_4191_ == 0 {
                                v___x_4186_ = v___x_4170_;
                                v_isShared_4187_ = v_isSharedCheck_4191_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4184_);
                                lean_dec(v___x_4170_);
                                v___x_4186_ = lean_box(0);
                                v_isShared_4187_ = v_isSharedCheck_4191_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_4152_);
                    lean_dec_ref_known(v___x_4143_, 14);
                    if v_isShared_4155_ == 0 {
                        lean_ctor_set(v___x_4154_, 0, v_a_4145_);
                        v___x_4193_ = v___x_4154_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4194_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4194_, 0, v_a_4145_);
                        v___x_4193_ = v_reuseFailAlloc_4194_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4161_;
            }
            4 => {
                v_fst_4175_ = lean_ctor_get(v_a_4171_, 0);
                lean_inc(v_fst_4175_);
                lean_dec(v_a_4171_);
                if lean_obj_tag(v_fst_4175_) == 0 {
                    if v_isShared_4174_ == 0 {
                        lean_ctor_set(v___x_4173_, 0, v_a_4145_);
                        v___x_4177_ = v___x_4173_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4178_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4145_);
                        v___x_4177_ = v_reuseFailAlloc_4178_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4145_);
                    v_val_4179_ = lean_ctor_get(v_fst_4175_, 0);
                    lean_inc(v_val_4179_);
                    lean_dec_ref_known(v_fst_4175_, 1);
                    if v_isShared_4174_ == 0 {
                        lean_ctor_set(v___x_4173_, 0, v_val_4179_);
                        v___x_4181_ = v___x_4173_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4182_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_val_4179_);
                        v___x_4181_ = v_reuseFailAlloc_4182_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4177_;
            }
            6 => {
                return v___x_4181_;
            }
            7 => {
                if v_isShared_4187_ == 0 {
                    v___x_4189_ = v___x_4186_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
                    v___x_4189_ = v_reuseFailAlloc_4190_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4189_;
            }
            9 => {
                return v___x_4193_;
            }
            10 => {
                if v_isShared_4199_ == 0 {
                    v___x_4201_ = v___x_4198_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
                    v___x_4201_ = v_reuseFailAlloc_4202_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(
    mut v_upperBound_4210_: *mut LeanObject,
    mut v_val_4211_: *mut LeanObject,
    mut v___x_4212_: *mut LeanObject,
    mut v___x_4213_: u8,
    mut v___x_4214_: *mut LeanObject,
    mut v___x_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
    mut v_b_4217_: *mut LeanObject,
    mut v___y_4218_: *mut LeanObject,
    mut v___y_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: u8 = 0;
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4247_: u8 = 0;
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4252_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v_a_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v___y_4268_: u8 = 0;
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: u8 = 0;
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: u8 = 0;
    let mut v___x_4273_: u8 = 0;
    let mut v_a_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4281_: u8 = 0;
    let mut v_a_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4285_: u8 = 0;
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4289_: u8 = 0;
    let mut v_a_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4297_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4228_ = lean_nat_dec_lt(v_a_4216_, v_upperBound_4210_);
                if v___x_4228_ == 0 {
                    lean_dec(v_a_4216_);
                    v___x_4229_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4229_, 0, v_b_4217_);
                    return v___x_4229_;
                } else {
                    lean_dec_ref(v_b_4217_);
                    v_numParams_4230_ = lean_ctor_get(v_val_4211_, 0);
                    v___x_4231_ = l_Lean_instInhabitedExpr;
                    v___x_4232_ = lean_unsigned_to_nat(1);
                    v___x_4233_ = lean_nat_add(v_numParams_4230_, v___x_4232_);
                    v___x_4234_ = lean_nat_add(v___x_4233_, v_a_4216_);
                    lean_dec(v___x_4233_);
                    v___x_4235_ = lean_array_get_borrowed(v___x_4231_, v___x_4212_, v___x_4234_);
                    lean_dec(v___x_4234_);
                    lean_inc(v___y_4221_);
                    lean_inc_ref(v___y_4220_);
                    lean_inc(v___y_4219_);
                    lean_inc_ref(v___y_4218_);
                    lean_inc(v___x_4235_);
                    v___x_4236_ = lean_infer_type(
                        v___x_4235_,
                        v___y_4218_,
                        v___y_4219_,
                        v___y_4220_,
                        v___y_4221_,
                    );
                    if lean_obj_tag(v___x_4236_) == 0 {
                        v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
                        lean_inc(v_a_4237_);
                        lean_dec_ref_known(v___x_4236_, 1);
                        v___x_4238_ = l_Lean_Meta_isClass_x3f(
                            v_a_4237_,
                            v___y_4218_,
                            v___y_4219_,
                            v___y_4220_,
                            v___y_4221_,
                        );
                        if lean_obj_tag(v___x_4238_) == 0 {
                            v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
                            lean_inc(v_a_4239_);
                            lean_dec_ref_known(v___x_4238_, 1);
                            v___x_4240_ = lean_box(0);
                            v___x_4241_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__1;
                            v___x_4242_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3;
                            v___x_4243_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_a_4239_, v___x_4242_);
                            lean_dec(v_a_4239_);
                            if v___x_4243_ == 0 {
                                v_a_4224_ = v___x_4241_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v___y_4221_);
                                lean_inc_ref(v___y_4220_);
                                lean_inc(v___y_4219_);
                                lean_inc_ref(v___y_4218_);
                                lean_inc(v___x_4235_);
                                v___x_4244_ = lean_whnf(
                                    v___x_4235_,
                                    v___y_4218_,
                                    v___y_4219_,
                                    v___y_4220_,
                                    v___y_4221_,
                                );
                                if lean_obj_tag(v___x_4244_) == 0 {
                                    v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
                                    lean_inc(v_a_4245_);
                                    lean_dec_ref_known(v___x_4244_, 1);
                                    v___x_4269_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5;
                                    v___x_4270_ = l_Lean_Expr_isAppOf(v_a_4245_, v___x_4269_);
                                    if v___x_4270_ == 0 {
                                        v___x_4271_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7;
                                        v___x_4272_ = l_Lean_Expr_isAppOf(v_a_4245_, v___x_4271_);
                                        v___y_4268_ = v___x_4272_;
                                        state = 7;
                                        continue;
                                    } else {
                                        v___x_4273_ = lean_nat_dec_eq(v___x_4214_, v___x_4215_);
                                        v___y_4268_ = v___x_4273_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_4216_);
                                    v_a_4274_ = lean_ctor_get(v___x_4244_, 0);
                                    v_isSharedCheck_4281_ = (!lean_is_exclusive(v___x_4244_)) as u8;
                                    if v_isSharedCheck_4281_ == 0 {
                                        v___x_4276_ = v___x_4244_;
                                        v_isShared_4277_ = v_isSharedCheck_4281_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4274_);
                                        lean_dec(v___x_4244_);
                                        v___x_4276_ = lean_box(0);
                                        v_isShared_4277_ = v_isSharedCheck_4281_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_4216_);
                            v_a_4282_ = lean_ctor_get(v___x_4238_, 0);
                            v_isSharedCheck_4289_ = (!lean_is_exclusive(v___x_4238_)) as u8;
                            if v_isSharedCheck_4289_ == 0 {
                                v___x_4284_ = v___x_4238_;
                                v_isShared_4285_ = v_isSharedCheck_4289_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_4282_);
                                lean_dec(v___x_4238_);
                                v___x_4284_ = lean_box(0);
                                v_isShared_4285_ = v_isSharedCheck_4289_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4216_);
                        v_a_4290_ = lean_ctor_get(v___x_4236_, 0);
                        v_isSharedCheck_4297_ = (!lean_is_exclusive(v___x_4236_)) as u8;
                        if v_isSharedCheck_4297_ == 0 {
                            v___x_4292_ = v___x_4236_;
                            v_isShared_4293_ = v_isSharedCheck_4297_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_4290_);
                            lean_dec(v___x_4236_);
                            v___x_4292_ = lean_box(0);
                            v_isShared_4293_ = v_isSharedCheck_4297_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4225_ = lean_unsigned_to_nat(1);
                v___x_4226_ = lean_nat_add(v_a_4216_, v___x_4225_);
                lean_dec(v_a_4216_);
                lean_inc_ref(v_a_4224_);
                v_a_4216_ = v___x_4226_;
                v_b_4217_ = v_a_4224_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_4247_ == 0 {
                    lean_dec(v_a_4245_);
                    v_a_4224_ = v___x_4241_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_a_4216_);
                    lean_inc_ref(v___y_4220_);
                    v___x_4248_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_a_4245_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
                    if lean_obj_tag(v___x_4248_) == 0 {
                        v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
                        v_isSharedCheck_4258_ = (!lean_is_exclusive(v___x_4248_)) as u8;
                        if v_isSharedCheck_4258_ == 0 {
                            v___x_4251_ = v___x_4248_;
                            v_isShared_4252_ = v_isSharedCheck_4258_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4249_);
                            lean_dec(v___x_4248_);
                            v___x_4251_ = lean_box(0);
                            v_isShared_4252_ = v_isSharedCheck_4258_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4259_ = lean_ctor_get(v___x_4248_, 0);
                        v_isSharedCheck_4266_ = (!lean_is_exclusive(v___x_4248_)) as u8;
                        if v_isSharedCheck_4266_ == 0 {
                            v___x_4261_ = v___x_4248_;
                            v_isShared_4262_ = v_isSharedCheck_4266_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4259_);
                            lean_dec(v___x_4248_);
                            v___x_4261_ = lean_box(0);
                            v_isShared_4262_ = v_isSharedCheck_4266_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_4253_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4253_, 0, v_a_4249_);
                v___x_4254_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4254_, 0, v___x_4253_);
                lean_ctor_set(v___x_4254_, 1, v___x_4240_);
                if v_isShared_4252_ == 0 {
                    lean_ctor_set(v___x_4251_, 0, v___x_4254_);
                    v___x_4256_ = v___x_4251_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
                    v___x_4256_ = v_reuseFailAlloc_4257_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4256_;
            }
            5 => {
                if v_isShared_4262_ == 0 {
                    v___x_4264_ = v___x_4261_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
                    v___x_4264_ = v_reuseFailAlloc_4265_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4264_;
            }
            7 => {
                if v___y_4268_ == 0 {
                    v___y_4247_ = v___x_4243_;
                    state = 2;
                    continue;
                } else {
                    v___y_4247_ = v___x_4213_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                if v_isShared_4277_ == 0 {
                    v___x_4279_ = v___x_4276_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
                    v___x_4279_ = v_reuseFailAlloc_4280_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4279_;
            }
            10 => {
                if v_isShared_4285_ == 0 {
                    v___x_4287_ = v___x_4284_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
                    v___x_4287_ = v_reuseFailAlloc_4288_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4287_;
            }
            12 => {
                if v_isShared_4293_ == 0 {
                    v___x_4295_ = v___x_4292_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4296_, 0, v_a_4290_);
                    v___x_4295_ = v_reuseFailAlloc_4296_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4295_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___boxed(
    mut v_upperBound_4298_: *mut LeanObject,
    mut v_val_4299_: *mut LeanObject,
    mut v___x_4300_: *mut LeanObject,
    mut v___x_4301_: *mut LeanObject,
    mut v___x_4302_: *mut LeanObject,
    mut v___x_4303_: *mut LeanObject,
    mut v_a_4304_: *mut LeanObject,
    mut v_b_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7093__boxed_4311_: u8 = 0;
    let mut v_res_4312_: *mut LeanObject = core::ptr::null_mut();
    v___x_7093__boxed_4311_ = (lean_unbox(v___x_4301_) as u8);
    v_res_4312_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_upperBound_4298_, v_val_4299_, v___x_4300_, v___x_7093__boxed_4311_, v___x_4302_, v___x_4303_, v_a_4304_, v_b_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
    lean_dec(v___y_4309_);
    lean_dec_ref(v___y_4308_);
    lean_dec(v___y_4307_);
    lean_dec_ref(v___y_4306_);
    lean_dec(v___x_4303_);
    lean_dec(v___x_4302_);
    lean_dec_ref(v___x_4300_);
    lean_dec_ref(v_val_4299_);
    lean_dec(v_upperBound_4298_);
    return v_res_4312_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure___boxed(
    mut v_inst_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
    mut v_a_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
    mut v_a_4317_: *mut LeanObject,
    mut v_a_4318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4319_: *mut LeanObject = core::ptr::null_mut();
    v_res_4319_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(
            v_inst_4313_,
            v_a_4314_,
            v_a_4315_,
            v_a_4316_,
            v_a_4317_,
        );
    lean_dec(v_a_4317_);
    lean_dec(v_a_4315_);
    lean_dec_ref(v_a_4314_);
    return v_res_4319_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(
    mut v_upperBound_4320_: *mut LeanObject,
    mut v_val_4321_: *mut LeanObject,
    mut v___x_4322_: *mut LeanObject,
    mut v___x_4323_: u8,
    mut v___x_4324_: *mut LeanObject,
    mut v___x_4325_: *mut LeanObject,
    mut v_inst_4326_: *mut LeanObject,
    mut v_R_4327_: *mut LeanObject,
    mut v_a_4328_: *mut LeanObject,
    mut v_b_4329_: *mut LeanObject,
    mut v_c_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
    mut v___y_4332_: *mut LeanObject,
    mut v___y_4333_: *mut LeanObject,
    mut v___y_4334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    v___x_4336_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg(v_upperBound_4320_, v_val_4321_, v___x_4322_, v___x_4323_, v___x_4324_, v___x_4325_, v_a_4328_, v_b_4329_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
    return v___x_4336_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___boxed(
    mut v_upperBound_4337_: *mut LeanObject,
    mut v_val_4338_: *mut LeanObject,
    mut v___x_4339_: *mut LeanObject,
    mut v___x_4340_: *mut LeanObject,
    mut v___x_4341_: *mut LeanObject,
    mut v___x_4342_: *mut LeanObject,
    mut v_inst_4343_: *mut LeanObject,
    mut v_R_4344_: *mut LeanObject,
    mut v_a_4345_: *mut LeanObject,
    mut v_b_4346_: *mut LeanObject,
    mut v_c_4347_: *mut LeanObject,
    mut v___y_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7439__boxed_4353_: u8 = 0;
    let mut v_res_4354_: *mut LeanObject = core::ptr::null_mut();
    v___x_7439__boxed_4353_ = (lean_unbox(v___x_4340_) as u8);
    v_res_4354_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2(v_upperBound_4337_, v_val_4338_, v___x_4339_, v___x_7439__boxed_4353_, v___x_4341_, v___x_4342_, v_inst_4343_, v_R_4344_, v_a_4345_, v_b_4346_, v_c_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
    lean_dec(v___y_4351_);
    lean_dec_ref(v___y_4350_);
    lean_dec(v___y_4349_);
    lean_dec_ref(v___y_4348_);
    lean_dec(v___x_4342_);
    lean_dec(v___x_4341_);
    lean_dec_ref(v___x_4339_);
    lean_dec_ref(v_val_4338_);
    lean_dec(v_upperBound_4337_);
    return v_res_4354_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(
    mut v_msg_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
    mut v___y_4359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4366_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4361_ = lean_ctor_get(v___y_4358_, 5);
                v___x_4362_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_);
                v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
                v_isSharedCheck_4371_ = (!lean_is_exclusive(v___x_4362_)) as u8;
                if v_isSharedCheck_4371_ == 0 {
                    v___x_4365_ = v___x_4362_;
                    v_isShared_4366_ = v_isSharedCheck_4371_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4363_);
                    lean_dec(v___x_4362_);
                    v___x_4365_ = lean_box(0);
                    v_isShared_4366_ = v_isSharedCheck_4371_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4361_);
                v___x_4367_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4367_, 0, v_ref_4361_);
                lean_ctor_set(v___x_4367_, 1, v_a_4363_);
                if v_isShared_4366_ == 0 {
                    lean_ctor_set_tag(v___x_4365_, 1);
                    lean_ctor_set(v___x_4365_, 0, v___x_4367_);
                    v___x_4369_ = v___x_4365_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4367_);
                    v___x_4369_ = v_reuseFailAlloc_4370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg___boxed(
    mut v_msg_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4378_: *mut LeanObject = core::ptr::null_mut();
    v_res_4378_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(
        v_msg_4372_,
        v___y_4373_,
        v___y_4374_,
        v___y_4375_,
        v___y_4376_,
    );
    lean_dec(v___y_4376_);
    lean_dec_ref(v___y_4375_);
    lean_dec(v___y_4374_);
    lean_dec_ref(v___y_4373_);
    return v_res_4378_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2() -> *mut LeanObject {
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut LeanObject = core::ptr::null_mut();
    v___x_4382_ = lean_box(0);
    v___x_4383_ = l_Lean_Elab_Tactic_elabNativeDecideCore___closed__1;
    v___x_4384_ = l_Lean_mkConst(v___x_4383_, v___x_4382_);
    return v___x_4384_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4() -> *mut LeanObject {
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    v___x_4386_ = l_Lean_Elab_Tactic_elabNativeDecideCore___closed__3;
    v___x_4387_ = l_Lean_stringToMessageData(v___x_4386_);
    return v___x_4387_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6() -> *mut LeanObject {
    let mut v___x_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    v___x_4389_ = l_Lean_Elab_Tactic_elabNativeDecideCore___closed__5;
    v___x_4390_ = l_Lean_stringToMessageData(v___x_4389_);
    return v___x_4390_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8() -> *mut LeanObject {
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut LeanObject = core::ptr::null_mut();
    v___x_4392_ = l_Lean_Elab_Tactic_elabNativeDecideCore___closed__7;
    v___x_4393_ = l_Lean_stringToMessageData(v___x_4392_);
    return v___x_4393_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabNativeDecideCore(
    mut v_tacticName_4394_: *mut LeanObject,
    mut v_expectedType_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
    mut v_a_4397_: *mut LeanObject,
    mut v_a_4398_: *mut LeanObject,
    mut v_a_4399_: *mut LeanObject,
    mut v_a_4400_: *mut LeanObject,
    mut v_a_4401_: *mut LeanObject,
    mut v_a_4402_: *mut LeanObject,
    mut v_a_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4409_: u8 = 0;
    let mut v_ref_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4417_: u8 = 0;
    let mut v_prf_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut v_a_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut v_reuseFailAlloc_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_expectedType_4395_);
                v___x_4405_ = l_Lean_Meta_mkDecide(
                    v_expectedType_4395_,
                    v_a_4400_,
                    v_a_4401_,
                    v_a_4402_,
                    v_a_4403_,
                );
                if lean_obj_tag(v___x_4405_) == 0 {
                    v_a_4406_ = lean_ctor_get(v___x_4405_, 0);
                    v_isSharedCheck_4445_ = (!lean_is_exclusive(v___x_4405_)) as u8;
                    if v_isSharedCheck_4445_ == 0 {
                        v___x_4408_ = v___x_4405_;
                        v_isShared_4409_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4406_);
                        lean_dec(v___x_4405_);
                        v___x_4408_ = lean_box(0);
                        v_isShared_4409_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_expectedType_4395_);
                    lean_dec(v_tacticName_4394_);
                    return v___x_4405_;
                }
            }
            1 => {
                v_ref_4410_ = lean_ctor_get(v_a_4402_, 5);
                lean_inc(v_ref_4410_);
                if v_isShared_4409_ == 0 {
                    lean_ctor_set_tag(v___x_4408_, 1);
                    lean_ctor_set(v___x_4408_, 0, v_ref_4410_);
                    v___x_4412_ = v___x_4408_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_ref_4410_);
                    v___x_4412_ = v_reuseFailAlloc_4444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_a_4406_);
                lean_inc(v_tacticName_4394_);
                v___x_4413_ = l_Lean_Meta_nativeEqTrue(
                    v_tacticName_4394_,
                    v_a_4406_,
                    v___x_4412_,
                    v_a_4400_,
                    v_a_4401_,
                    v_a_4402_,
                    v_a_4403_,
                );
                lean_dec_ref(v___x_4412_);
                if lean_obj_tag(v___x_4413_) == 0 {
                    v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4435_ = (!lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4435_ == 0 {
                        v___x_4416_ = v___x_4413_;
                        v_isShared_4417_ = v_isSharedCheck_4435_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4414_);
                        lean_dec(v___x_4413_);
                        v___x_4416_ = lean_box(0);
                        v_isShared_4417_ = v_isSharedCheck_4435_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4406_);
                    lean_dec_ref(v_expectedType_4395_);
                    lean_dec(v_tacticName_4394_);
                    v_a_4436_ = lean_ctor_get(v___x_4413_, 0);
                    v_isSharedCheck_4443_ = (!lean_is_exclusive(v___x_4413_)) as u8;
                    if v_isSharedCheck_4443_ == 0 {
                        v___x_4438_ = v___x_4413_;
                        v_isShared_4439_ = v_isSharedCheck_4443_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4436_);
                        lean_dec(v___x_4413_);
                        v___x_4438_ = lean_box(0);
                        v_isShared_4439_ = v_isSharedCheck_4443_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_4414_) == 0 {
                    lean_dec(v_tacticName_4394_);
                    v_prf_4418_ = lean_ctor_get(v_a_4414_, 0);
                    lean_inc_ref(v_prf_4418_);
                    lean_dec_ref_known(v_a_4414_, 1);
                    v___x_4419_ = l_Lean_Expr_appArg_x21(v_a_4406_);
                    lean_dec(v_a_4406_);
                    v___x_4420_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__2,
                    );
                    v___x_4421_ =
                        l_Lean_mkApp3(v___x_4420_, v_expectedType_4395_, v___x_4419_, v_prf_4418_);
                    if v_isShared_4417_ == 0 {
                        lean_ctor_set(v___x_4416_, 0, v___x_4421_);
                        v___x_4423_ = v___x_4416_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4421_);
                        v___x_4423_ = v_reuseFailAlloc_4424_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4416_);
                    lean_dec(v_a_4406_);
                    v___x_4425_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once
                        ),
                        _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4,
                    );
                    v___x_4426_ = l_Lean_MessageData_ofName(v_tacticName_4394_);
                    v___x_4427_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4427_, 0, v___x_4425_);
                    lean_ctor_set(v___x_4427_, 1, v___x_4426_);
                    v___x_4428_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6_once
                        ),
                        _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__6,
                    );
                    v___x_4429_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4429_, 0, v___x_4427_);
                    lean_ctor_set(v___x_4429_, 1, v___x_4428_);
                    v___x_4430_ = l_Lean_indentExpr(v_expectedType_4395_);
                    v___x_4431_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4431_, 0, v___x_4429_);
                    lean_ctor_set(v___x_4431_, 1, v___x_4430_);
                    v___x_4432_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once
                        ),
                        _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8,
                    );
                    v___x_4433_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4433_, 0, v___x_4431_);
                    lean_ctor_set(v___x_4433_, 1, v___x_4432_);
                    v___x_4434_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_4433_, v_a_4400_, v_a_4401_, v_a_4402_, v_a_4403_);
                    return v___x_4434_;
                }
            }
            4 => {
                return v___x_4423_;
            }
            5 => {
                if v_isShared_4439_ == 0 {
                    v___x_4441_ = v___x_4438_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
                    v___x_4441_ = v_reuseFailAlloc_4442_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabNativeDecideCore___boxed(
    mut v_tacticName_4446_: *mut LeanObject,
    mut v_expectedType_4447_: *mut LeanObject,
    mut v_a_4448_: *mut LeanObject,
    mut v_a_4449_: *mut LeanObject,
    mut v_a_4450_: *mut LeanObject,
    mut v_a_4451_: *mut LeanObject,
    mut v_a_4452_: *mut LeanObject,
    mut v_a_4453_: *mut LeanObject,
    mut v_a_4454_: *mut LeanObject,
    mut v_a_4455_: *mut LeanObject,
    mut v_a_4456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4457_: *mut LeanObject = core::ptr::null_mut();
    v_res_4457_ = l_Lean_Elab_Tactic_elabNativeDecideCore(
        v_tacticName_4446_,
        v_expectedType_4447_,
        v_a_4448_,
        v_a_4449_,
        v_a_4450_,
        v_a_4451_,
        v_a_4452_,
        v_a_4453_,
        v_a_4454_,
        v_a_4455_,
    );
    lean_dec(v_a_4455_);
    lean_dec_ref(v_a_4454_);
    lean_dec(v_a_4453_);
    lean_dec_ref(v_a_4452_);
    lean_dec(v_a_4451_);
    lean_dec_ref(v_a_4450_);
    lean_dec(v_a_4449_);
    lean_dec_ref(v_a_4448_);
    return v_res_4457_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(
    mut v_00_u03b1_4458_: *mut LeanObject,
    mut v_msg_4459_: *mut LeanObject,
    mut v___y_4460_: *mut LeanObject,
    mut v___y_4461_: *mut LeanObject,
    mut v___y_4462_: *mut LeanObject,
    mut v___y_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
    mut v___y_4467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4469_: *mut LeanObject = core::ptr::null_mut();
    v___x_4469_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(
        v_msg_4459_,
        v___y_4464_,
        v___y_4465_,
        v___y_4466_,
        v___y_4467_,
    );
    return v___x_4469_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___boxed(
    mut v_00_u03b1_4470_: *mut LeanObject,
    mut v_msg_4471_: *mut LeanObject,
    mut v___y_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
    mut v___y_4476_: *mut LeanObject,
    mut v___y_4477_: *mut LeanObject,
    mut v___y_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4481_: *mut LeanObject = core::ptr::null_mut();
    v_res_4481_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0(
        v_00_u03b1_4470_,
        v_msg_4471_,
        v___y_4472_,
        v___y_4473_,
        v___y_4474_,
        v___y_4475_,
        v___y_4476_,
        v___y_4477_,
        v___y_4478_,
        v___y_4479_,
    );
    lean_dec(v___y_4479_);
    lean_dec_ref(v___y_4478_);
    lean_dec(v___y_4477_);
    lean_dec_ref(v___y_4476_);
    lean_dec(v___y_4475_);
    lean_dec_ref(v___y_4474_);
    lean_dec(v___y_4473_);
    lean_dec_ref(v___y_4472_);
    return v_res_4481_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(
    mut v_opts_4482_: *mut LeanObject,
    mut v_opt_4483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    v_name_4484_ = lean_ctor_get(v_opt_4483_, 0);
    v_defValue_4485_ = lean_ctor_get(v_opt_4483_, 1);
    v_map_4486_ = lean_ctor_get(v_opts_4482_, 0);
    v___x_4487_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4486_,
            v_name_4484_,
        );
    if lean_obj_tag(v___x_4487_) == 0 {
        lean_inc(v_defValue_4485_);
        return v_defValue_4485_;
    } else {
        let mut v_val_4488_: *mut LeanObject = core::ptr::null_mut();
        v_val_4488_ = lean_ctor_get(v___x_4487_, 0);
        lean_inc(v_val_4488_);
        lean_dec_ref_known(v___x_4487_, 1);
        if lean_obj_tag(v_val_4488_) == 3 {
            let mut v_v_4489_: *mut LeanObject = core::ptr::null_mut();
            v_v_4489_ = lean_ctor_get(v_val_4488_, 0);
            lean_inc(v_v_4489_);
            lean_dec_ref_known(v_val_4488_, 1);
            return v_v_4489_;
        } else {
            lean_dec(v_val_4488_);
            lean_inc(v_defValue_4485_);
            return v_defValue_4485_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1___boxed(
    mut v_opts_4490_: *mut LeanObject,
    mut v_opt_4491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4492_: *mut LeanObject = core::ptr::null_mut();
    v_res_4492_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v_opts_4490_, v_opt_4491_);
    lean_dec_ref(v_opt_4491_);
    lean_dec_ref(v_opts_4490_);
    return v_res_4492_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(
    mut v_x_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v_unused_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4515_: u8 = 0;
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4519_: u8 = 0;
    let mut v_a_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4524_: u8 = 0;
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4528_: u8 = 0;
    let mut v_unused_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v_a_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4499_ = l_Lean_Meta_saveState___redArg(v___y_4495_, v___y_4497_);
                if lean_obj_tag(v___x_4499_) == 0 {
                    v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
                    lean_inc(v_a_4500_);
                    lean_dec_ref_known(v___x_4499_, 1);
                    lean_inc(v___y_4497_);
                    lean_inc_ref(v___y_4496_);
                    lean_inc(v___y_4495_);
                    lean_inc_ref(v___y_4494_);
                    v_r_4501_ = lean_apply_5(
                        v_x_4493_,
                        v___y_4494_,
                        v___y_4495_,
                        v___y_4496_,
                        v___y_4497_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_4501_) == 0 {
                        v_a_4502_ = lean_ctor_get(v_r_4501_, 0);
                        lean_inc(v_a_4502_);
                        lean_dec_ref_known(v_r_4501_, 1);
                        v___x_4503_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_4500_,
                            v___y_4495_,
                            v___y_4497_,
                        );
                        lean_dec(v_a_4500_);
                        if lean_obj_tag(v___x_4503_) == 0 {
                            v_isSharedCheck_4510_ = (!lean_is_exclusive(v___x_4503_)) as u8;
                            if v_isSharedCheck_4510_ == 0 {
                                v_unused_4511_ = lean_ctor_get(v___x_4503_, 0);
                                lean_dec(v_unused_4511_);
                                v___x_4505_ = v___x_4503_;
                                v_isShared_4506_ = v_isSharedCheck_4510_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_4503_);
                                v___x_4505_ = lean_box(0);
                                v_isShared_4506_ = v_isSharedCheck_4510_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4502_);
                            v_a_4512_ = lean_ctor_get(v___x_4503_, 0);
                            v_isSharedCheck_4519_ = (!lean_is_exclusive(v___x_4503_)) as u8;
                            if v_isSharedCheck_4519_ == 0 {
                                v___x_4514_ = v___x_4503_;
                                v_isShared_4515_ = v_isSharedCheck_4519_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4512_);
                                lean_dec(v___x_4503_);
                                v___x_4514_ = lean_box(0);
                                v_isShared_4515_ = v_isSharedCheck_4519_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_4520_ = lean_ctor_get(v_r_4501_, 0);
                        lean_inc(v_a_4520_);
                        lean_dec_ref_known(v_r_4501_, 1);
                        v___x_4521_ = l_Lean_Meta_SavedState_restore___redArg(
                            v_a_4500_,
                            v___y_4495_,
                            v___y_4497_,
                        );
                        lean_dec(v_a_4500_);
                        if lean_obj_tag(v___x_4521_) == 0 {
                            v_isSharedCheck_4528_ = (!lean_is_exclusive(v___x_4521_)) as u8;
                            if v_isSharedCheck_4528_ == 0 {
                                v_unused_4529_ = lean_ctor_get(v___x_4521_, 0);
                                lean_dec(v_unused_4529_);
                                v___x_4523_ = v___x_4521_;
                                v_isShared_4524_ = v_isSharedCheck_4528_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v___x_4521_);
                                v___x_4523_ = lean_box(0);
                                v_isShared_4524_ = v_isSharedCheck_4528_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4520_);
                            v_a_4530_ = lean_ctor_get(v___x_4521_, 0);
                            v_isSharedCheck_4537_ = (!lean_is_exclusive(v___x_4521_)) as u8;
                            if v_isSharedCheck_4537_ == 0 {
                                v___x_4532_ = v___x_4521_;
                                v_isShared_4533_ = v_isSharedCheck_4537_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_4530_);
                                lean_dec(v___x_4521_);
                                v___x_4532_ = lean_box(0);
                                v_isShared_4533_ = v_isSharedCheck_4537_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_x_4493_);
                    v_a_4538_ = lean_ctor_get(v___x_4499_, 0);
                    v_isSharedCheck_4545_ = (!lean_is_exclusive(v___x_4499_)) as u8;
                    if v_isSharedCheck_4545_ == 0 {
                        v___x_4540_ = v___x_4499_;
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4538_);
                        lean_dec(v___x_4499_);
                        v___x_4540_ = lean_box(0);
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4506_ == 0 {
                    lean_ctor_set(v___x_4505_, 0, v_a_4502_);
                    v___x_4508_ = v___x_4505_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4502_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4508_;
            }
            3 => {
                if v_isShared_4515_ == 0 {
                    v___x_4517_ = v___x_4514_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
                    v___x_4517_ = v_reuseFailAlloc_4518_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4517_;
            }
            5 => {
                if v_isShared_4524_ == 0 {
                    lean_ctor_set_tag(v___x_4523_, 1);
                    lean_ctor_set(v___x_4523_, 0, v_a_4520_);
                    v___x_4526_ = v___x_4523_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4520_);
                    v___x_4526_ = v_reuseFailAlloc_4527_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4526_;
            }
            7 => {
                if v_isShared_4533_ == 0 {
                    v___x_4535_ = v___x_4532_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
                    v___x_4535_ = v_reuseFailAlloc_4536_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4535_;
            }
            9 => {
                if v_isShared_4541_ == 0 {
                    v___x_4543_ = v___x_4540_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg___boxed(
    mut v_x_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
    mut v___y_4548_: *mut LeanObject,
    mut v___y_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4552_: *mut LeanObject = core::ptr::null_mut();
    v_res_4552_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_x_4546_, v___y_4547_, v___y_4548_, v___y_4549_, v___y_4550_);
    lean_dec(v___y_4550_);
    lean_dec_ref(v___y_4549_);
    lean_dec(v___y_4548_);
    lean_dec_ref(v___y_4547_);
    return v_res_4552_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(
    mut v_00_u03b1_4553_: *mut LeanObject,
    mut v_x_4554_: *mut LeanObject,
    mut v___y_4555_: *mut LeanObject,
    mut v___y_4556_: *mut LeanObject,
    mut v___y_4557_: *mut LeanObject,
    mut v___y_4558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    v___x_4560_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v_x_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
    return v___x_4560_;
}
pub unsafe fn l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___boxed(
    mut v_00_u03b1_4561_: *mut LeanObject,
    mut v_x_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
    mut v___y_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4568_: *mut LeanObject = core::ptr::null_mut();
    v_res_4568_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6(v_00_u03b1_4561_, v_x_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
    lean_dec(v___y_4566_);
    lean_dec_ref(v___y_4565_);
    lean_dec(v___y_4564_);
    lean_dec_ref(v___y_4563_);
    return v_res_4568_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(
    mut v_cs_4569_: *mut LeanObject,
    mut v_n_4570_: *mut LeanObject,
    mut v_x_4571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    v___x_4572_ = lean_array_push(v_cs_4569_, v_n_4570_);
    return v___x_4572_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0___boxed(
    mut v_cs_4573_: *mut LeanObject,
    mut v_n_4574_: *mut LeanObject,
    mut v_x_4575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4576_: *mut LeanObject = core::ptr::null_mut();
    v_res_4576_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__0(
            v_cs_4573_, v_n_4574_, v_x_4575_,
        );
    lean_dec(v_x_4575_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(
    mut v_o_4580_: *mut LeanObject,
    mut v_k_4581_: *mut LeanObject,
    mut v_v_4582_: u8,
) -> *mut LeanObject {
    let mut v_map_4583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4584_: u8 = 0;
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: u8 = 0;
    let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4583_ = lean_ctor_get(v_o_4580_, 0);
                v_hasTrace_4584_ = lean_ctor_get_uint8(
                    v_o_4580_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4598_ = (!lean_is_exclusive(v_o_4580_)) as u8;
                if v_isSharedCheck_4598_ == 0 {
                    v___x_4586_ = v_o_4580_;
                    v_isShared_4587_ = v_isSharedCheck_4598_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_4583_);
                    lean_dec(v_o_4580_);
                    v___x_4586_ = lean_box(0);
                    v_isShared_4587_ = v_isSharedCheck_4598_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4588_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_4588_, 0 as u32, v_v_4582_);
                lean_inc(v_k_4581_);
                v___x_4589_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4581_, v___x_4588_, v_map_4583_);
                if v_hasTrace_4584_ == 0 {
                    v___x_4590_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___closed__1;
                    v___x_4591_ = l_Lean_Name_isPrefixOf(v___x_4590_, v_k_4581_);
                    lean_dec(v_k_4581_);
                    if v_isShared_4587_ == 0 {
                        lean_ctor_set(v___x_4586_, 0, v___x_4589_);
                        v___x_4593_ = v___x_4586_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4594_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4594_, 0, v___x_4589_);
                        v___x_4593_ = v_reuseFailAlloc_4594_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_4581_);
                    if v_isShared_4587_ == 0 {
                        lean_ctor_set(v___x_4586_, 0, v___x_4589_);
                        v___x_4596_ = v___x_4586_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4589_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_4597_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_4584_,
                        );
                        v___x_4596_ = v_reuseFailAlloc_4597_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_4593_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_4591_,
                );
                return v___x_4593_;
            }
            3 => {
                return v___x_4596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0___boxed(
    mut v_o_4599_: *mut LeanObject,
    mut v_k_4600_: *mut LeanObject,
    mut v_v_4601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_4602_: u8 = 0;
    let mut v_res_4603_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_4602_ = (lean_unbox(v_v_4601_) as u8);
    v_res_4603_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_o_4599_, v_k_4600_, v_v_boxed_4602_);
    return v_res_4603_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(
    mut v_opts_4604_: *mut LeanObject,
    mut v_opt_4605_: *mut LeanObject,
    mut v_val_4606_: u8,
) -> *mut LeanObject {
    let mut v_name_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    v_name_4607_ = lean_ctor_get(v_opt_4605_, 0);
    lean_inc(v_name_4607_);
    lean_dec_ref(v_opt_4605_);
    v___x_4608_ = l_Lean_Options_set___at___00Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0_spec__0(v_opts_4604_, v_name_4607_, v_val_4606_);
    return v___x_4608_;
}
pub unsafe fn l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0___boxed(
    mut v_opts_4609_: *mut LeanObject,
    mut v_opt_4610_: *mut LeanObject,
    mut v_val_4611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_4612_: u8 = 0;
    let mut v_res_4613_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_4612_ = (lean_unbox(v_val_4611_) as u8);
    v_res_4613_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_opts_4609_, v_opt_4610_, v_val_boxed_4612_);
    return v_res_4613_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(
    mut v_f_4614_: *mut LeanObject,
    mut v_keys_4615_: *mut LeanObject,
    mut v_vals_4616_: *mut LeanObject,
    mut v_i_4617_: *mut LeanObject,
    mut v_acc_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: u8 = 0;
    let mut v_k_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4619_ = lean_array_get_size(v_keys_4615_);
                v___x_4620_ = lean_nat_dec_lt(v_i_4617_, v___x_4619_);
                if v___x_4620_ == 0 {
                    lean_dec(v_i_4617_);
                    lean_dec(v_f_4614_);
                    return v_acc_4618_;
                } else {
                    v_k_4621_ = lean_array_fget_borrowed(v_keys_4615_, v_i_4617_);
                    v_v_4622_ = lean_array_fget_borrowed(v_vals_4616_, v_i_4617_);
                    lean_inc(v_f_4614_);
                    lean_inc(v_v_4622_);
                    lean_inc(v_k_4621_);
                    v___x_4623_ = lean_apply_3(v_f_4614_, v_acc_4618_, v_k_4621_, v_v_4622_);
                    v___x_4624_ = lean_unsigned_to_nat(1);
                    v___x_4625_ = lean_nat_add(v_i_4617_, v___x_4624_);
                    lean_dec(v_i_4617_);
                    v_i_4617_ = v___x_4625_;
                    v_acc_4618_ = v___x_4623_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg___boxed(
    mut v_f_4627_: *mut LeanObject,
    mut v_keys_4628_: *mut LeanObject,
    mut v_vals_4629_: *mut LeanObject,
    mut v_i_4630_: *mut LeanObject,
    mut v_acc_4631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4632_: *mut LeanObject = core::ptr::null_mut();
    v_res_4632_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_4627_, v_keys_4628_, v_vals_4629_, v_i_4630_, v_acc_4631_);
    lean_dec_ref(v_vals_4629_);
    lean_dec_ref(v_keys_4628_);
    return v_res_4632_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(
    mut v_f_4633_: *mut LeanObject,
    mut v_x_4634_: *mut LeanObject,
    mut v_x_4635_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4634_) == 0 {
        let mut v_es_4636_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4639_: u8 = 0;
        v_es_4636_ = lean_ctor_get(v_x_4634_, 0);
        v___x_4637_ = lean_unsigned_to_nat(0);
        v___x_4638_ = lean_array_get_size(v_es_4636_);
        v___x_4639_ = lean_nat_dec_lt(v___x_4637_, v___x_4638_);
        if v___x_4639_ == 0 {
            lean_dec(v_f_4633_);
            return v_x_4635_;
        } else {
            let mut v___x_4640_: u8 = 0;
            v___x_4640_ = lean_nat_dec_le(v___x_4638_, v___x_4638_);
            if v___x_4640_ == 0 {
                if v___x_4639_ == 0 {
                    lean_dec(v_f_4633_);
                    return v_x_4635_;
                } else {
                    let mut v___x_4641_: usize = 0;
                    let mut v___x_4642_: usize = 0;
                    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
                    v___x_4641_ = 0usize;
                    v___x_4642_ = lean_usize_of_nat(v___x_4638_);
                    v___x_4643_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_4633_, v_es_4636_, v___x_4641_, v___x_4642_, v_x_4635_);
                    return v___x_4643_;
                }
            } else {
                let mut v___x_4644_: usize = 0;
                let mut v___x_4645_: usize = 0;
                let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
                v___x_4644_ = 0usize;
                v___x_4645_ = lean_usize_of_nat(v___x_4638_);
                v___x_4646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_4633_, v_es_4636_, v___x_4644_, v___x_4645_, v_x_4635_);
                return v___x_4646_;
            }
        }
    } else {
        let mut v_ks_4647_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_4648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
        v_ks_4647_ = lean_ctor_get(v_x_4634_, 0);
        v_vs_4648_ = lean_ctor_get(v_x_4634_, 1);
        v___x_4649_ = lean_unsigned_to_nat(0);
        v___x_4650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_4633_, v_ks_4647_, v_vs_4648_, v___x_4649_, v_x_4635_);
        return v___x_4650_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(
    mut v_f_4651_: *mut LeanObject,
    mut v_as_4652_: *mut LeanObject,
    mut v_i_4653_: usize,
    mut v_stop_4654_: usize,
    mut v_b_4655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: usize = 0;
    let mut v___x_4659_: usize = 0;
    let mut v___x_4661_: u8 = 0;
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4661_ = lean_usize_dec_eq(v_i_4653_, v_stop_4654_);
                if v___x_4661_ == 0 {
                    v___x_4662_ = lean_array_uget_borrowed(v_as_4652_, v_i_4653_);
                    match lean_obj_tag(v___x_4662_) {
                        0 => {
                            v_key_4663_ = lean_ctor_get(v___x_4662_, 0);
                            v_val_4664_ = lean_ctor_get(v___x_4662_, 1);
                            lean_inc(v_f_4651_);
                            lean_inc(v_val_4664_);
                            lean_inc(v_key_4663_);
                            v___x_4665_ =
                                lean_apply_3(v_f_4651_, v_b_4655_, v_key_4663_, v_val_4664_);
                            v___y_4657_ = v___x_4665_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_4666_ = lean_ctor_get(v___x_4662_, 0);
                            lean_inc(v_f_4651_);
                            v___x_4667_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_4651_, v_node_4666_, v_b_4655_);
                            v___y_4657_ = v___x_4667_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_4657_ = v_b_4655_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_f_4651_);
                    return v_b_4655_;
                }
            }
            1 => {
                v___x_4658_ = 1usize;
                v___x_4659_ = lean_usize_add(v_i_4653_, v___x_4658_);
                v_i_4653_ = v___x_4659_;
                v_b_4655_ = v___y_4657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg___boxed(
    mut v_f_4668_: *mut LeanObject,
    mut v_as_4669_: *mut LeanObject,
    mut v_i_4670_: *mut LeanObject,
    mut v_stop_4671_: *mut LeanObject,
    mut v_b_4672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4673_: usize = 0;
    let mut v_stop_boxed_4674_: usize = 0;
    let mut v_res_4675_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4673_ = lean_unbox_usize(v_i_4670_);
    lean_dec(v_i_4670_);
    v_stop_boxed_4674_ = lean_unbox_usize(v_stop_4671_);
    lean_dec(v_stop_4671_);
    v_res_4675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_4668_, v_as_4669_, v_i_boxed_4673_, v_stop_boxed_4674_, v_b_4672_);
    lean_dec_ref(v_as_4669_);
    return v_res_4675_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg___boxed(
    mut v_f_4676_: *mut LeanObject,
    mut v_x_4677_: *mut LeanObject,
    mut v_x_4678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4679_: *mut LeanObject = core::ptr::null_mut();
    v_res_4679_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_4676_, v_x_4677_, v_x_4678_);
    lean_dec_ref(v_x_4677_);
    return v_res_4679_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0(
    mut v_f_4680_: *mut LeanObject,
    mut v_x1_4681_: *mut LeanObject,
    mut v_x2_4682_: *mut LeanObject,
    mut v_x3_4683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    v___x_4684_ = lean_apply_3(v_f_4680_, v_x1_4681_, v_x2_4682_, v_x3_4683_);
    return v___x_4684_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(
    mut v_map_4685_: *mut LeanObject,
    mut v_f_4686_: *mut LeanObject,
    mut v_init_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    v___f_4688_ = lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    lean_closure_set(v___f_4688_, 0, v_f_4686_);
    v___x_4689_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v___f_4688_, v_map_4685_, v_init_4687_);
    return v___x_4689_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg___boxed(
    mut v_map_4690_: *mut LeanObject,
    mut v_f_4691_: *mut LeanObject,
    mut v_init_4692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4693_: *mut LeanObject = core::ptr::null_mut();
    v_res_4693_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_4690_, v_f_4691_, v_init_4692_);
    lean_dec_ref(v_map_4690_);
    return v_res_4693_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(
    mut v_hi_4694_: *mut LeanObject,
    mut v_pivot_4695_: *mut LeanObject,
    mut v_as_4696_: *mut LeanObject,
    mut v_i_4697_: *mut LeanObject,
    mut v_k_4698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4699_: u8 = 0;
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: u8 = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4699_ = lean_nat_dec_lt(v_k_4698_, v_hi_4694_);
                if v___x_4699_ == 0 {
                    lean_dec(v_k_4698_);
                    v___x_4700_ = lean_array_fswap(v_as_4696_, v_i_4697_, v_hi_4694_);
                    v___x_4701_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4701_, 0, v_i_4697_);
                    lean_ctor_set(v___x_4701_, 1, v___x_4700_);
                    return v___x_4701_;
                } else {
                    v___x_4702_ = lean_array_fget_borrowed(v_as_4696_, v_k_4698_);
                    v___x_4703_ = l_Lean_Name_lt(v___x_4702_, v_pivot_4695_);
                    if v___x_4703_ == 0 {
                        v___x_4704_ = lean_unsigned_to_nat(1);
                        v___x_4705_ = lean_nat_add(v_k_4698_, v___x_4704_);
                        lean_dec(v_k_4698_);
                        v_k_4698_ = v___x_4705_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4707_ = lean_array_fswap(v_as_4696_, v_i_4697_, v_k_4698_);
                        v___x_4708_ = lean_unsigned_to_nat(1);
                        v___x_4709_ = lean_nat_add(v_i_4697_, v___x_4708_);
                        lean_dec(v_i_4697_);
                        v___x_4710_ = lean_nat_add(v_k_4698_, v___x_4708_);
                        lean_dec(v_k_4698_);
                        v_as_4696_ = v___x_4707_;
                        v_i_4697_ = v___x_4709_;
                        v_k_4698_ = v___x_4710_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg___boxed(
    mut v_hi_4712_: *mut LeanObject,
    mut v_pivot_4713_: *mut LeanObject,
    mut v_as_4714_: *mut LeanObject,
    mut v_i_4715_: *mut LeanObject,
    mut v_k_4716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4717_: *mut LeanObject = core::ptr::null_mut();
    v_res_4717_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(v_hi_4712_, v_pivot_4713_, v_as_4714_, v_i_4715_, v_k_4716_);
    lean_dec(v_pivot_4713_);
    lean_dec(v_hi_4712_);
    return v_res_4717_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(
    mut v_n_4718_: *mut LeanObject,
    mut v_as_4719_: *mut LeanObject,
    mut v_lo_4720_: *mut LeanObject,
    mut v_hi_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: u8 = 0;
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: u8 = 0;
    let mut v___x_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: u8 = 0;
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4733_ = lean_nat_dec_lt(v_lo_4720_, v_hi_4721_);
                if v___x_4733_ == 0 {
                    lean_dec(v_lo_4720_);
                    return v_as_4719_;
                } else {
                    v___x_4734_ = lean_nat_add(v_lo_4720_, v_hi_4721_);
                    v___x_4735_ = lean_unsigned_to_nat(1);
                    v_mid_4736_ = lean_nat_shiftr(v___x_4734_, v___x_4735_);
                    lean_dec(v___x_4734_);
                    v___x_4749_ = lean_array_fget_borrowed(v_as_4719_, v_mid_4736_);
                    v___x_4750_ = lean_array_fget_borrowed(v_as_4719_, v_lo_4720_);
                    v___x_4751_ = l_Lean_Name_lt(v___x_4749_, v___x_4750_);
                    if v___x_4751_ == 0 {
                        v___y_4744_ = v_as_4719_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4752_ = lean_array_fswap(v_as_4719_, v_lo_4720_, v_mid_4736_);
                        v___y_4744_ = v___x_4752_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_4724_ = lean_array_fget(v___y_4723_, v_hi_4721_);
                lean_inc_n(v_lo_4720_, 2);
                v___x_4725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(v_hi_4721_, v_pivot_4724_, v___y_4723_, v_lo_4720_, v_lo_4720_);
                lean_dec(v_pivot_4724_);
                v_fst_4726_ = lean_ctor_get(v___x_4725_, 0);
                lean_inc(v_fst_4726_);
                v_snd_4727_ = lean_ctor_get(v___x_4725_, 1);
                lean_inc(v_snd_4727_);
                lean_dec_ref(v___x_4725_);
                v___x_4728_ = lean_nat_dec_le(v_hi_4721_, v_fst_4726_);
                if v___x_4728_ == 0 {
                    v___x_4729_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_4718_, v_snd_4727_, v_lo_4720_, v_fst_4726_);
                    v___x_4730_ = lean_unsigned_to_nat(1);
                    v___x_4731_ = lean_nat_add(v_fst_4726_, v___x_4730_);
                    lean_dec(v_fst_4726_);
                    v_as_4719_ = v___x_4729_;
                    v_lo_4720_ = v___x_4731_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_4726_);
                    lean_dec(v_lo_4720_);
                    return v_snd_4727_;
                }
            }
            2 => {
                v___x_4739_ = lean_array_fget_borrowed(v___y_4738_, v_mid_4736_);
                v___x_4740_ = lean_array_fget_borrowed(v___y_4738_, v_hi_4721_);
                v___x_4741_ = l_Lean_Name_lt(v___x_4739_, v___x_4740_);
                if v___x_4741_ == 0 {
                    lean_dec(v_mid_4736_);
                    v___y_4723_ = v___y_4738_;
                    state = 1;
                    continue;
                } else {
                    v___x_4742_ = lean_array_fswap(v___y_4738_, v_mid_4736_, v_hi_4721_);
                    lean_dec(v_mid_4736_);
                    v___y_4723_ = v___x_4742_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_4745_ = lean_array_fget_borrowed(v___y_4744_, v_hi_4721_);
                v___x_4746_ = lean_array_fget_borrowed(v___y_4744_, v_lo_4720_);
                v___x_4747_ = l_Lean_Name_lt(v___x_4745_, v___x_4746_);
                if v___x_4747_ == 0 {
                    v___y_4738_ = v___y_4744_;
                    state = 2;
                    continue;
                } else {
                    v___x_4748_ = lean_array_fswap(v___y_4744_, v_lo_4720_, v_hi_4721_);
                    v___y_4738_ = v___x_4748_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg___boxed(
    mut v_n_4753_: *mut LeanObject,
    mut v_as_4754_: *mut LeanObject,
    mut v_lo_4755_: *mut LeanObject,
    mut v_hi_4756_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4757_: *mut LeanObject = core::ptr::null_mut();
    v_res_4757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_4753_, v_as_4754_, v_lo_4755_, v_hi_4756_);
    lean_dec(v_hi_4756_);
    lean_dec(v_n_4753_);
    return v_res_4757_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(
    mut v_a_4758_: *mut LeanObject,
    mut v_a_4759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4765_: u8 = 0;
    let mut v___x_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4758_) == 0 {
                    v___x_4760_ = l_List_reverse___redArg(v_a_4759_);
                    return v___x_4760_;
                } else {
                    v_head_4761_ = lean_ctor_get(v_a_4758_, 0);
                    v_tail_4762_ = lean_ctor_get(v_a_4758_, 1);
                    v_isSharedCheck_4771_ = (!lean_is_exclusive(v_a_4758_)) as u8;
                    if v_isSharedCheck_4771_ == 0 {
                        v___x_4764_ = v_a_4758_;
                        v_isShared_4765_ = v_isSharedCheck_4771_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4762_);
                        lean_inc(v_head_4761_);
                        lean_dec(v_a_4758_);
                        v___x_4764_ = lean_box(0);
                        v_isShared_4765_ = v_isSharedCheck_4771_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4766_ = l_Lean_mkLevelParam(v_head_4761_);
                if v_isShared_4765_ == 0 {
                    lean_ctor_set(v___x_4764_, 1, v_a_4759_);
                    lean_ctor_set(v___x_4764_, 0, v___x_4766_);
                    v___x_4768_ = v___x_4764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 0, v___x_4766_);
                    lean_ctor_set(v_reuseFailAlloc_4770_, 1, v_a_4759_);
                    v___x_4768_ = v_reuseFailAlloc_4770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4758_ = v_tail_4762_;
                v_a_4759_ = v___x_4768_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(
    mut v_msg_4772_: *mut LeanObject,
    mut v___y_4773_: *mut LeanObject,
    mut v___y_4774_: *mut LeanObject,
    mut v___y_4775_: *mut LeanObject,
    mut v___y_4776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4783_: u8 = 0;
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4778_ = lean_ctor_get(v___y_4775_, 5);
                v___x_4779_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__0(v_msg_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
                v_a_4780_ = lean_ctor_get(v___x_4779_, 0);
                v_isSharedCheck_4788_ = (!lean_is_exclusive(v___x_4779_)) as u8;
                if v_isSharedCheck_4788_ == 0 {
                    v___x_4782_ = v___x_4779_;
                    v_isShared_4783_ = v_isSharedCheck_4788_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4780_);
                    lean_dec(v___x_4779_);
                    v___x_4782_ = lean_box(0);
                    v_isShared_4783_ = v_isSharedCheck_4788_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4778_);
                v___x_4784_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4784_, 0, v_ref_4778_);
                lean_ctor_set(v___x_4784_, 1, v_a_4780_);
                if v_isShared_4783_ == 0 {
                    lean_ctor_set_tag(v___x_4782_, 1);
                    lean_ctor_set(v___x_4782_, 0, v___x_4784_);
                    v___x_4786_ = v___x_4782_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4787_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4787_, 0, v___x_4784_);
                    v___x_4786_ = v_reuseFailAlloc_4787_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4786_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg___boxed(
    mut v_msg_4789_: *mut LeanObject,
    mut v___y_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
    mut v___y_4793_: *mut LeanObject,
    mut v___y_4794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4795_: *mut LeanObject = core::ptr::null_mut();
    v_res_4795_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(v_msg_4789_, v___y_4790_, v___y_4791_, v___y_4792_, v___y_4793_);
    lean_dec(v___y_4793_);
    lean_dec_ref(v___y_4792_);
    lean_dec(v___y_4791_);
    lean_dec_ref(v___y_4790_);
    return v_res_4795_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(
    mut v_ref_4796_: *mut LeanObject,
    mut v_msg_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4815_: u8 = 0;
    let mut v_cancelTk_x3f_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4817_: u8 = 0;
    let mut v_inheritedTraceOptions_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4803_ = lean_ctor_get(v___y_4800_, 0);
    v_fileMap_4804_ = lean_ctor_get(v___y_4800_, 1);
    v_options_4805_ = lean_ctor_get(v___y_4800_, 2);
    v_currRecDepth_4806_ = lean_ctor_get(v___y_4800_, 3);
    v_maxRecDepth_4807_ = lean_ctor_get(v___y_4800_, 4);
    v_ref_4808_ = lean_ctor_get(v___y_4800_, 5);
    v_currNamespace_4809_ = lean_ctor_get(v___y_4800_, 6);
    v_openDecls_4810_ = lean_ctor_get(v___y_4800_, 7);
    v_initHeartbeats_4811_ = lean_ctor_get(v___y_4800_, 8);
    v_maxHeartbeats_4812_ = lean_ctor_get(v___y_4800_, 9);
    v_quotContext_4813_ = lean_ctor_get(v___y_4800_, 10);
    v_currMacroScope_4814_ = lean_ctor_get(v___y_4800_, 11);
    v_diag_4815_ = lean_ctor_get_uint8(
        v___y_4800_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4816_ = lean_ctor_get(v___y_4800_, 12);
    v_suppressElabErrors_4817_ = lean_ctor_get_uint8(
        v___y_4800_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4818_ = lean_ctor_get(v___y_4800_, 13);
    v_ref_4819_ = l_Lean_replaceRef(v_ref_4796_, v_ref_4808_);
    lean_inc_ref(v_inheritedTraceOptions_4818_);
    lean_inc(v_cancelTk_x3f_4816_);
    lean_inc(v_currMacroScope_4814_);
    lean_inc(v_quotContext_4813_);
    lean_inc(v_maxHeartbeats_4812_);
    lean_inc(v_initHeartbeats_4811_);
    lean_inc(v_openDecls_4810_);
    lean_inc(v_currNamespace_4809_);
    lean_inc(v_maxRecDepth_4807_);
    lean_inc(v_currRecDepth_4806_);
    lean_inc_ref(v_options_4805_);
    lean_inc_ref(v_fileMap_4804_);
    lean_inc_ref(v_fileName_4803_);
    v___x_4820_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4820_, 0, v_fileName_4803_);
    lean_ctor_set(v___x_4820_, 1, v_fileMap_4804_);
    lean_ctor_set(v___x_4820_, 2, v_options_4805_);
    lean_ctor_set(v___x_4820_, 3, v_currRecDepth_4806_);
    lean_ctor_set(v___x_4820_, 4, v_maxRecDepth_4807_);
    lean_ctor_set(v___x_4820_, 5, v_ref_4819_);
    lean_ctor_set(v___x_4820_, 6, v_currNamespace_4809_);
    lean_ctor_set(v___x_4820_, 7, v_openDecls_4810_);
    lean_ctor_set(v___x_4820_, 8, v_initHeartbeats_4811_);
    lean_ctor_set(v___x_4820_, 9, v_maxHeartbeats_4812_);
    lean_ctor_set(v___x_4820_, 10, v_quotContext_4813_);
    lean_ctor_set(v___x_4820_, 11, v_currMacroScope_4814_);
    lean_ctor_set(v___x_4820_, 12, v_cancelTk_x3f_4816_);
    lean_ctor_set(v___x_4820_, 13, v_inheritedTraceOptions_4818_);
    lean_ctor_set_uint8(
        v___x_4820_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4815_,
    );
    lean_ctor_set_uint8(
        v___x_4820_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4817_,
    );
    v___x_4821_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(v_msg_4797_, v___y_4798_, v___y_4799_, v___x_4820_, v___y_4801_);
    lean_dec_ref_known(v___x_4820_, 14);
    return v___x_4821_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg___boxed(
    mut v_ref_4822_: *mut LeanObject,
    mut v_msg_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4829_: *mut LeanObject = core::ptr::null_mut();
    v_res_4829_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(v_ref_4822_, v_msg_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
    lean_dec(v___y_4827_);
    lean_dec_ref(v___y_4826_);
    lean_dec(v___y_4825_);
    lean_dec_ref(v___y_4824_);
    lean_dec(v_ref_4822_);
    return v_res_4829_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4830_: *mut LeanObject = core::ptr::null_mut();
    v___x_4830_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4830_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    v___x_4831_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__0);
    v___x_4832_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4832_, 0, v___x_4831_);
    return v___x_4832_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut LeanObject = core::ptr::null_mut();
    v___x_4833_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1);
    v___x_4834_ = lean_unsigned_to_nat(0);
    v___x_4835_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4835_, 0, v___x_4834_);
    lean_ctor_set(v___x_4835_, 1, v___x_4834_);
    lean_ctor_set(v___x_4835_, 2, v___x_4834_);
    lean_ctor_set(v___x_4835_, 3, v___x_4834_);
    lean_ctor_set(v___x_4835_, 4, v___x_4833_);
    lean_ctor_set(v___x_4835_, 5, v___x_4833_);
    lean_ctor_set(v___x_4835_, 6, v___x_4833_);
    lean_ctor_set(v___x_4835_, 7, v___x_4833_);
    lean_ctor_set(v___x_4835_, 8, v___x_4833_);
    lean_ctor_set(v___x_4835_, 9, v___x_4833_);
    return v___x_4835_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    v___x_4836_ = lean_unsigned_to_nat(32);
    v___x_4837_ = lean_mk_empty_array_with_capacity(v___x_4836_);
    v___x_4838_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4838_, 0, v___x_4837_);
    return v___x_4838_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4839_: usize = 0;
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    v___x_4839_ = 5usize;
    v___x_4840_ = lean_unsigned_to_nat(0);
    v___x_4841_ = lean_unsigned_to_nat(32);
    v___x_4842_ = lean_mk_empty_array_with_capacity(v___x_4841_);
    v___x_4843_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__3);
    v___x_4844_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4844_, 0, v___x_4843_);
    lean_ctor_set(v___x_4844_, 1, v___x_4842_);
    lean_ctor_set(v___x_4844_, 2, v___x_4840_);
    lean_ctor_set(v___x_4844_, 3, v___x_4840_);
    lean_ctor_set_usize(v___x_4844_, 4, v___x_4839_);
    return v___x_4844_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    v___x_4845_ = lean_box(1);
    v___x_4846_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__4);
    v___x_4847_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__1);
    v___x_4848_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4848_, 0, v___x_4847_);
    lean_ctor_set(v___x_4848_, 1, v___x_4846_);
    lean_ctor_set(v___x_4848_, 2, v___x_4845_);
    return v___x_4848_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    v___x_4850_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__6;
    v___x_4851_ = l_Lean_stringToMessageData(v___x_4850_);
    return v___x_4851_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_4853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    v___x_4853_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__8;
    v___x_4854_ = l_Lean_stringToMessageData(v___x_4853_);
    return v___x_4854_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    v___x_4856_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__10;
    v___x_4857_ = l_Lean_stringToMessageData(v___x_4856_);
    return v___x_4857_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    v___x_4859_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__12;
    v___x_4860_ = l_Lean_stringToMessageData(v___x_4859_);
    return v___x_4860_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    v___x_4862_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__14;
    v___x_4863_ = l_Lean_stringToMessageData(v___x_4862_);
    return v___x_4863_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    v___x_4865_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__16;
    v___x_4866_ = l_Lean_stringToMessageData(v___x_4865_);
    return v___x_4866_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    v___x_4868_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__18;
    v___x_4869_ = l_Lean_stringToMessageData(v___x_4868_);
    return v___x_4869_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(
    mut v_msg_4870_: *mut LeanObject,
    mut v_declHint_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    let mut v_isExporting_4877_: u8 = 0;
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: u8 = 0;
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v___x_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4931_: u8 = 0;
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4874_ = lean_st_ref_get(v___y_4872_);
                v_env_4875_ = lean_ctor_get(v___x_4874_, 0);
                lean_inc_ref(v_env_4875_);
                lean_dec(v___x_4874_);
                v___x_4876_ = l_Lean_Name_isAnonymous(v_declHint_4871_);
                if v___x_4876_ == 0 {
                    v_isExporting_4877_ = lean_ctor_get_uint8(
                        v_env_4875_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_4877_ == 0 {
                        lean_dec_ref(v_env_4875_);
                        lean_dec(v_declHint_4871_);
                        v___x_4878_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4878_, 0, v_msg_4870_);
                        return v___x_4878_;
                    } else {
                        lean_inc_ref(v_env_4875_);
                        v___x_4879_ = l_Lean_Environment_setExporting(v_env_4875_, v___x_4876_);
                        lean_inc(v_declHint_4871_);
                        lean_inc_ref(v___x_4879_);
                        v___x_4880_ = l_Lean_Environment_contains(
                            v___x_4879_,
                            v_declHint_4871_,
                            v_isExporting_4877_,
                        );
                        if v___x_4880_ == 0 {
                            lean_dec_ref(v___x_4879_);
                            lean_dec_ref(v_env_4875_);
                            lean_dec(v_declHint_4871_);
                            v___x_4881_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4881_, 0, v_msg_4870_);
                            return v___x_4881_;
                        } else {
                            v___x_4882_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__2);
                            v___x_4883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__5);
                            v___x_4884_ = l_Lean_Options_empty;
                            v___x_4885_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_4885_, 0, v___x_4879_);
                            lean_ctor_set(v___x_4885_, 1, v___x_4882_);
                            lean_ctor_set(v___x_4885_, 2, v___x_4883_);
                            lean_ctor_set(v___x_4885_, 3, v___x_4884_);
                            lean_inc(v_declHint_4871_);
                            v___x_4886_ =
                                l_Lean_MessageData_ofConstName(v_declHint_4871_, v___x_4876_);
                            v_c_4887_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_4887_, 0, v___x_4885_);
                            lean_ctor_set(v_c_4887_, 1, v___x_4886_);
                            v___x_4888_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_4875_,
                                v_declHint_4871_,
                            );
                            if lean_obj_tag(v___x_4888_) == 0 {
                                lean_dec_ref(v_env_4875_);
                                lean_dec(v_declHint_4871_);
                                v___x_4889_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7);
                                v___x_4890_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4890_, 0, v___x_4889_);
                                lean_ctor_set(v___x_4890_, 1, v_c_4887_);
                                v___x_4891_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__9);
                                v___x_4892_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4892_, 0, v___x_4890_);
                                lean_ctor_set(v___x_4892_, 1, v___x_4891_);
                                v___x_4893_ = l_Lean_MessageData_note(v___x_4892_);
                                v___x_4894_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4894_, 0, v_msg_4870_);
                                lean_ctor_set(v___x_4894_, 1, v___x_4893_);
                                v___x_4895_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4895_, 0, v___x_4894_);
                                return v___x_4895_;
                            } else {
                                v_val_4896_ = lean_ctor_get(v___x_4888_, 0);
                                v_isSharedCheck_4931_ = (!lean_is_exclusive(v___x_4888_)) as u8;
                                if v_isSharedCheck_4931_ == 0 {
                                    v___x_4898_ = v___x_4888_;
                                    v_isShared_4899_ = v_isSharedCheck_4931_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_4896_);
                                    lean_dec(v___x_4888_);
                                    v___x_4898_ = lean_box(0);
                                    v_isShared_4899_ = v_isSharedCheck_4931_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_4875_);
                    lean_dec(v_declHint_4871_);
                    v___x_4932_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4932_, 0, v_msg_4870_);
                    return v___x_4932_;
                }
            }
            1 => {
                v___x_4900_ = lean_box(0);
                v___x_4901_ = l_Lean_Environment_header(v_env_4875_);
                lean_dec_ref(v_env_4875_);
                v___x_4902_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4901_);
                v_mod_4903_ = lean_array_get(v___x_4900_, v___x_4902_, v_val_4896_);
                lean_dec(v_val_4896_);
                lean_dec_ref(v___x_4902_);
                v___x_4904_ = l_Lean_isPrivateName(v_declHint_4871_);
                lean_dec(v_declHint_4871_);
                if v___x_4904_ == 0 {
                    v___x_4905_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__11);
                    v___x_4906_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4906_, 0, v___x_4905_);
                    lean_ctor_set(v___x_4906_, 1, v_c_4887_);
                    v___x_4907_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__13);
                    v___x_4908_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4908_, 0, v___x_4906_);
                    lean_ctor_set(v___x_4908_, 1, v___x_4907_);
                    v___x_4909_ = l_Lean_MessageData_ofName(v_mod_4903_);
                    v___x_4910_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4910_, 0, v___x_4908_);
                    lean_ctor_set(v___x_4910_, 1, v___x_4909_);
                    v___x_4911_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15);
                    v___x_4912_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4912_, 0, v___x_4910_);
                    lean_ctor_set(v___x_4912_, 1, v___x_4911_);
                    v___x_4913_ = l_Lean_MessageData_note(v___x_4912_);
                    v___x_4914_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4914_, 0, v_msg_4870_);
                    lean_ctor_set(v___x_4914_, 1, v___x_4913_);
                    if v_isShared_4899_ == 0 {
                        lean_ctor_set_tag(v___x_4898_, 0);
                        lean_ctor_set(v___x_4898_, 0, v___x_4914_);
                        v___x_4916_ = v___x_4898_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4914_);
                        v___x_4916_ = v_reuseFailAlloc_4917_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4918_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__7);
                    v___x_4919_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4919_, 0, v___x_4918_);
                    lean_ctor_set(v___x_4919_, 1, v_c_4887_);
                    v___x_4920_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__17);
                    v___x_4921_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4921_, 0, v___x_4919_);
                    lean_ctor_set(v___x_4921_, 1, v___x_4920_);
                    v___x_4922_ = l_Lean_MessageData_ofName(v_mod_4903_);
                    v___x_4923_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4923_, 0, v___x_4921_);
                    lean_ctor_set(v___x_4923_, 1, v___x_4922_);
                    v___x_4924_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__19);
                    v___x_4925_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4925_, 0, v___x_4923_);
                    lean_ctor_set(v___x_4925_, 1, v___x_4924_);
                    v___x_4926_ = l_Lean_MessageData_note(v___x_4925_);
                    v___x_4927_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4927_, 0, v_msg_4870_);
                    lean_ctor_set(v___x_4927_, 1, v___x_4926_);
                    if v_isShared_4899_ == 0 {
                        lean_ctor_set_tag(v___x_4898_, 0);
                        lean_ctor_set(v___x_4898_, 0, v___x_4927_);
                        v___x_4929_ = v___x_4898_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4930_, 0, v___x_4927_);
                        v___x_4929_ = v_reuseFailAlloc_4930_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4916_;
            }
            3 => {
                return v___x_4929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___boxed(
    mut v_msg_4933_: *mut LeanObject,
    mut v_declHint_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4937_: *mut LeanObject = core::ptr::null_mut();
    v_res_4937_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(v_msg_4933_, v_declHint_4934_, v___y_4935_);
    lean_dec(v___y_4935_);
    return v_res_4937_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16(
    mut v_msg_4938_: *mut LeanObject,
    mut v_declHint_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4949_: u8 = 0;
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4955_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4945_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(v_msg_4938_, v_declHint_4939_, v___y_4943_);
                v_a_4946_ = lean_ctor_get(v___x_4945_, 0);
                v_isSharedCheck_4955_ = (!lean_is_exclusive(v___x_4945_)) as u8;
                if v_isSharedCheck_4955_ == 0 {
                    v___x_4948_ = v___x_4945_;
                    v_isShared_4949_ = v_isSharedCheck_4955_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4946_);
                    lean_dec(v___x_4945_);
                    v___x_4948_ = lean_box(0);
                    v_isShared_4949_ = v_isSharedCheck_4955_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4950_ = l_Lean_unknownIdentifierMessageTag;
                v___x_4951_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_4951_, 0, v___x_4950_);
                lean_ctor_set(v___x_4951_, 1, v_a_4946_);
                if v_isShared_4949_ == 0 {
                    lean_ctor_set(v___x_4948_, 0, v___x_4951_);
                    v___x_4953_ = v___x_4948_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4954_, 0, v___x_4951_);
                    v___x_4953_ = v_reuseFailAlloc_4954_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4953_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16___boxed(
    mut v_msg_4956_: *mut LeanObject,
    mut v_declHint_4957_: *mut LeanObject,
    mut v___y_4958_: *mut LeanObject,
    mut v___y_4959_: *mut LeanObject,
    mut v___y_4960_: *mut LeanObject,
    mut v___y_4961_: *mut LeanObject,
    mut v___y_4962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4963_: *mut LeanObject = core::ptr::null_mut();
    v_res_4963_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16(v_msg_4956_, v_declHint_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_);
    lean_dec(v___y_4961_);
    lean_dec_ref(v___y_4960_);
    lean_dec(v___y_4959_);
    lean_dec_ref(v___y_4958_);
    return v_res_4963_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(
    mut v_ref_4964_: *mut LeanObject,
    mut v_msg_4965_: *mut LeanObject,
    mut v_declHint_4966_: *mut LeanObject,
    mut v___y_4967_: *mut LeanObject,
    mut v___y_4968_: *mut LeanObject,
    mut v___y_4969_: *mut LeanObject,
    mut v___y_4970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    v___x_4972_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16(v_msg_4965_, v_declHint_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_);
    v_a_4973_ = lean_ctor_get(v___x_4972_, 0);
    lean_inc(v_a_4973_);
    lean_dec_ref(v___x_4972_);
    v___x_4974_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(v_ref_4964_, v_a_4973_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_);
    return v___x_4974_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg___boxed(
    mut v_ref_4975_: *mut LeanObject,
    mut v_msg_4976_: *mut LeanObject,
    mut v_declHint_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
    mut v___y_4980_: *mut LeanObject,
    mut v___y_4981_: *mut LeanObject,
    mut v___y_4982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4983_: *mut LeanObject = core::ptr::null_mut();
    v_res_4983_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(v_ref_4975_, v_msg_4976_, v_declHint_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
    lean_dec(v___y_4981_);
    lean_dec_ref(v___y_4980_);
    lean_dec(v___y_4979_);
    lean_dec_ref(v___y_4978_);
    lean_dec(v_ref_4975_);
    return v_res_4983_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    v___x_4985_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__0;
    v___x_4986_ = l_Lean_stringToMessageData(v___x_4985_);
    return v___x_4986_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut LeanObject = core::ptr::null_mut();
    v___x_4988_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__2;
    v___x_4989_ = l_Lean_stringToMessageData(v___x_4988_);
    return v___x_4989_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(
    mut v_ref_4990_: *mut LeanObject,
    mut v_constName_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
    mut v___y_4995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: u8 = 0;
    let mut v___x_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    v___x_4997_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__1);
    v___x_4998_ = 0;
    lean_inc(v_constName_4991_);
    v___x_4999_ = l_Lean_MessageData_ofConstName(v_constName_4991_, v___x_4998_);
    v___x_5000_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5000_, 0, v___x_4997_);
    lean_ctor_set(v___x_5000_, 1, v___x_4999_);
    v___x_5001_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3);
    v___x_5002_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_5002_, 0, v___x_5000_);
    lean_ctor_set(v___x_5002_, 1, v___x_5001_);
    v___x_5003_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(v_ref_4990_, v___x_5002_, v_constName_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_);
    return v___x_5003_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___boxed(
    mut v_ref_5004_: *mut LeanObject,
    mut v_constName_5005_: *mut LeanObject,
    mut v___y_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5011_: *mut LeanObject = core::ptr::null_mut();
    v_res_5011_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_5004_, v_constName_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
    lean_dec(v___y_5009_);
    lean_dec_ref(v___y_5008_);
    lean_dec(v___y_5007_);
    lean_dec_ref(v___y_5006_);
    lean_dec(v_ref_5004_);
    return v_res_5011_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(
    mut v_constName_5012_: *mut LeanObject,
    mut v___y_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
    mut v___y_5015_: *mut LeanObject,
    mut v___y_5016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5018_ = lean_ctor_get(v___y_5015_, 5);
    v___x_5019_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_5018_, v_constName_5012_, v___y_5013_, v___y_5014_, v___y_5015_, v___y_5016_);
    return v___x_5019_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_constName_5020_: *mut LeanObject,
    mut v___y_5021_: *mut LeanObject,
    mut v___y_5022_: *mut LeanObject,
    mut v___y_5023_: *mut LeanObject,
    mut v___y_5024_: *mut LeanObject,
    mut v___y_5025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5026_: *mut LeanObject = core::ptr::null_mut();
    v_res_5026_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_5020_, v___y_5021_, v___y_5022_, v___y_5023_, v___y_5024_);
    lean_dec(v___y_5024_);
    lean_dec_ref(v___y_5023_);
    lean_dec(v___y_5022_);
    lean_dec_ref(v___y_5021_);
    return v_res_5026_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(
    mut v_constName_5027_: *mut LeanObject,
    mut v___y_5028_: *mut LeanObject,
    mut v___y_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
    mut v___y_5031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: u8 = 0;
    let mut v___x_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5041_: u8 = 0;
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5033_ = lean_st_ref_get(v___y_5031_);
                v_env_5034_ = lean_ctor_get(v___x_5033_, 0);
                lean_inc_ref(v_env_5034_);
                lean_dec(v___x_5033_);
                v___x_5035_ = 0;
                lean_inc(v_constName_5027_);
                v___x_5036_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_5034_,
                    v_constName_5027_,
                    v___x_5035_,
                );
                if lean_obj_tag(v___x_5036_) == 0 {
                    v___x_5037_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_5027_, v___y_5028_, v___y_5029_, v___y_5030_, v___y_5031_);
                    return v___x_5037_;
                } else {
                    lean_dec(v_constName_5027_);
                    v_val_5038_ = lean_ctor_get(v___x_5036_, 0);
                    v_isSharedCheck_5045_ = (!lean_is_exclusive(v___x_5036_)) as u8;
                    if v_isSharedCheck_5045_ == 0 {
                        v___x_5040_ = v___x_5036_;
                        v_isShared_5041_ = v_isSharedCheck_5045_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_5038_);
                        lean_dec(v___x_5036_);
                        v___x_5040_ = lean_box(0);
                        v_isShared_5041_ = v_isSharedCheck_5045_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5041_ == 0 {
                    lean_ctor_set_tag(v___x_5040_, 0);
                    v___x_5043_ = v___x_5040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5044_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5044_, 0, v_val_5038_);
                    v___x_5043_ = v_reuseFailAlloc_5044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3___boxed(
    mut v_constName_5046_: *mut LeanObject,
    mut v___y_5047_: *mut LeanObject,
    mut v___y_5048_: *mut LeanObject,
    mut v___y_5049_: *mut LeanObject,
    mut v___y_5050_: *mut LeanObject,
    mut v___y_5051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5052_: *mut LeanObject = core::ptr::null_mut();
    v_res_5052_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_5046_, v___y_5047_, v___y_5048_, v___y_5049_, v___y_5050_);
    lean_dec(v___y_5050_);
    lean_dec_ref(v___y_5049_);
    lean_dec(v___y_5048_);
    lean_dec_ref(v___y_5047_);
    return v_res_5052_;
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(
    mut v_constName_5053_: *mut LeanObject,
    mut v___y_5054_: *mut LeanObject,
    mut v___y_5055_: *mut LeanObject,
    mut v___y_5056_: *mut LeanObject,
    mut v___y_5057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5063_: u8 = 0;
    let mut v_levelParams_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut v_a_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5075_: u8 = 0;
    let mut v___x_5077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_5053_);
                v___x_5059_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3(v_constName_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
                if lean_obj_tag(v___x_5059_) == 0 {
                    v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
                    v_isSharedCheck_5071_ = (!lean_is_exclusive(v___x_5059_)) as u8;
                    if v_isSharedCheck_5071_ == 0 {
                        v___x_5062_ = v___x_5059_;
                        v_isShared_5063_ = v_isSharedCheck_5071_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5060_);
                        lean_dec(v___x_5059_);
                        v___x_5062_ = lean_box(0);
                        v_isShared_5063_ = v_isSharedCheck_5071_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_5053_);
                    v_a_5072_ = lean_ctor_get(v___x_5059_, 0);
                    v_isSharedCheck_5079_ = (!lean_is_exclusive(v___x_5059_)) as u8;
                    if v_isSharedCheck_5079_ == 0 {
                        v___x_5074_ = v___x_5059_;
                        v_isShared_5075_ = v_isSharedCheck_5079_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5072_);
                        lean_dec(v___x_5059_);
                        v___x_5074_ = lean_box(0);
                        v_isShared_5075_ = v_isSharedCheck_5079_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_5064_ = lean_ctor_get(v_a_5060_, 1);
                lean_inc(v_levelParams_5064_);
                lean_dec(v_a_5060_);
                v___x_5065_ = lean_box(0);
                v___x_5066_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__4(v_levelParams_5064_, v___x_5065_);
                v___x_5067_ = l_Lean_mkConst(v_constName_5053_, v___x_5066_);
                if v_isShared_5063_ == 0 {
                    lean_ctor_set(v___x_5062_, 0, v___x_5067_);
                    v___x_5069_ = v___x_5062_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5070_, 0, v___x_5067_);
                    v___x_5069_ = v_reuseFailAlloc_5070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5069_;
            }
            3 => {
                if v_isShared_5075_ == 0 {
                    v___x_5077_ = v___x_5074_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5078_, 0, v_a_5072_);
                    v___x_5077_ = v_reuseFailAlloc_5078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2___boxed(
    mut v_constName_5080_: *mut LeanObject,
    mut v___y_5081_: *mut LeanObject,
    mut v___y_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5086_: *mut LeanObject = core::ptr::null_mut();
    v_res_5086_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v_constName_5080_, v___y_5081_, v___y_5082_, v___y_5083_, v___y_5084_);
    lean_dec(v___y_5084_);
    lean_dec_ref(v___y_5083_);
    lean_dec(v___y_5082_);
    lean_dec_ref(v___y_5081_);
    return v_res_5086_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(
    mut v_as_5087_: *mut LeanObject,
    mut v_i_5088_: usize,
    mut v_stop_5089_: usize,
    mut v_b_5090_: *mut LeanObject,
    mut v___y_5091_: *mut LeanObject,
    mut v___y_5092_: *mut LeanObject,
    mut v___y_5093_: *mut LeanObject,
    mut v___y_5094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5096_: u8 = 0;
    let mut v___x_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: usize = 0;
    let mut v___x_5107_: usize = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: u8 = 0;
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5119_: u8 = 0;
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5123_: u8 = 0;
    let mut v_a_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5127_: u8 = 0;
    let mut v___x_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5131_: u8 = 0;
    let mut v_a_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5135_: u8 = 0;
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5139_: u8 = 0;
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5096_ = lean_usize_dec_eq(v_i_5088_, v_stop_5089_);
                if v___x_5096_ == 0 {
                    v___x_5097_ = lean_array_uget_borrowed(v_as_5087_, v_i_5088_);
                    lean_inc(v___x_5097_);
                    v___x_5098_ = l_Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2(v___x_5097_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
                    if lean_obj_tag(v___x_5098_) == 0 {
                        v_a_5099_ = lean_ctor_get(v___x_5098_, 0);
                        lean_inc_n(v_a_5099_, 2);
                        lean_dec_ref_known(v___x_5098_, 1);
                        lean_inc(v___y_5094_);
                        lean_inc_ref(v___y_5093_);
                        lean_inc(v___y_5092_);
                        lean_inc_ref(v___y_5091_);
                        v___x_5100_ = lean_infer_type(
                            v_a_5099_,
                            v___y_5091_,
                            v___y_5092_,
                            v___y_5093_,
                            v___y_5094_,
                        );
                        if lean_obj_tag(v___x_5100_) == 0 {
                            v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
                            lean_inc(v_a_5101_);
                            lean_dec_ref_known(v___x_5100_, 1);
                            v___x_5102_ = l_Lean_Meta_isClass_x3f(
                                v_a_5101_,
                                v___y_5091_,
                                v___y_5092_,
                                v___y_5093_,
                                v___y_5094_,
                            );
                            if lean_obj_tag(v___x_5102_) == 0 {
                                v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
                                lean_inc(v_a_5103_);
                                lean_dec_ref_known(v___x_5102_, 1);
                                v___x_5109_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__3;
                                v___x_5110_ = l_Option_instBEq_beq___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__1(v_a_5103_, v___x_5109_);
                                lean_dec(v_a_5103_);
                                if v___x_5110_ == 0 {
                                    lean_dec(v_a_5099_);
                                    v_a_5105_ = v_b_5090_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_5111_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3);
                                    v___x_5112_ = l_Lean_MessageData_ofConst(v_a_5099_);
                                    v___x_5113_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5113_, 0, v___x_5111_);
                                    lean_ctor_set(v___x_5113_, 1, v___x_5112_);
                                    v___x_5114_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_5114_, 0, v___x_5113_);
                                    lean_ctor_set(v___x_5114_, 1, v___x_5111_);
                                    v___x_5115_ = lean_array_push(v_b_5090_, v___x_5114_);
                                    v_a_5105_ = v___x_5115_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5099_);
                                lean_dec_ref(v_b_5090_);
                                v_a_5116_ = lean_ctor_get(v___x_5102_, 0);
                                v_isSharedCheck_5123_ = (!lean_is_exclusive(v___x_5102_)) as u8;
                                if v_isSharedCheck_5123_ == 0 {
                                    v___x_5118_ = v___x_5102_;
                                    v_isShared_5119_ = v_isSharedCheck_5123_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_5116_);
                                    lean_dec(v___x_5102_);
                                    v___x_5118_ = lean_box(0);
                                    v_isShared_5119_ = v_isSharedCheck_5123_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5099_);
                            lean_dec_ref(v_b_5090_);
                            v_a_5124_ = lean_ctor_get(v___x_5100_, 0);
                            v_isSharedCheck_5131_ = (!lean_is_exclusive(v___x_5100_)) as u8;
                            if v_isSharedCheck_5131_ == 0 {
                                v___x_5126_ = v___x_5100_;
                                v_isShared_5127_ = v_isSharedCheck_5131_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5124_);
                                lean_dec(v___x_5100_);
                                v___x_5126_ = lean_box(0);
                                v_isShared_5127_ = v_isSharedCheck_5131_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_b_5090_);
                        v_a_5132_ = lean_ctor_get(v___x_5098_, 0);
                        v_isSharedCheck_5139_ = (!lean_is_exclusive(v___x_5098_)) as u8;
                        if v_isSharedCheck_5139_ == 0 {
                            v___x_5134_ = v___x_5098_;
                            v_isShared_5135_ = v_isSharedCheck_5139_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5132_);
                            lean_dec(v___x_5098_);
                            v___x_5134_ = lean_box(0);
                            v_isShared_5135_ = v_isSharedCheck_5139_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_5140_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5140_, 0, v_b_5090_);
                    return v___x_5140_;
                }
            }
            1 => {
                v___x_5106_ = 1usize;
                v___x_5107_ = lean_usize_add(v_i_5088_, v___x_5106_);
                v_i_5088_ = v___x_5107_;
                v_b_5090_ = v_a_5105_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_5119_ == 0 {
                    v___x_5121_ = v___x_5118_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
                    v___x_5121_ = v_reuseFailAlloc_5122_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5121_;
            }
            4 => {
                if v_isShared_5127_ == 0 {
                    v___x_5129_ = v___x_5126_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5130_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5130_, 0, v_a_5124_);
                    v___x_5129_ = v_reuseFailAlloc_5130_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5129_;
            }
            6 => {
                if v_isShared_5135_ == 0 {
                    v___x_5137_ = v___x_5134_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5138_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5138_, 0, v_a_5132_);
                    v___x_5137_ = v_reuseFailAlloc_5138_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5137_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8___boxed(
    mut v_as_5141_: *mut LeanObject,
    mut v_i_5142_: *mut LeanObject,
    mut v_stop_5143_: *mut LeanObject,
    mut v_b_5144_: *mut LeanObject,
    mut v___y_5145_: *mut LeanObject,
    mut v___y_5146_: *mut LeanObject,
    mut v___y_5147_: *mut LeanObject,
    mut v___y_5148_: *mut LeanObject,
    mut v___y_5149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5150_: usize = 0;
    let mut v_stop_boxed_5151_: usize = 0;
    let mut v_res_5152_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5150_ = lean_unbox_usize(v_i_5142_);
    lean_dec(v_i_5142_);
    v_stop_boxed_5151_ = lean_unbox_usize(v_stop_5143_);
    lean_dec(v_stop_5143_);
    v_res_5152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_5141_, v_i_boxed_5150_, v_stop_boxed_5151_, v_b_5144_, v___y_5145_, v___y_5146_, v___y_5147_, v___y_5148_);
    lean_dec(v___y_5148_);
    lean_dec_ref(v___y_5147_);
    lean_dec(v___y_5146_);
    lean_dec_ref(v___y_5145_);
    lean_dec_ref(v_as_5141_);
    return v_res_5152_;
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(
    mut v_as_5155_: *mut LeanObject,
    mut v_start_5156_: *mut LeanObject,
    mut v_stop_5157_: *mut LeanObject,
    mut v___y_5158_: *mut LeanObject,
    mut v___y_5159_: *mut LeanObject,
    mut v___y_5160_: *mut LeanObject,
    mut v___y_5161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: u8 = 0;
    v___x_5163_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___closed__0;
    v___x_5164_ = lean_nat_dec_lt(v_start_5156_, v_stop_5157_);
    if v___x_5164_ == 0 {
        let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
        v___x_5165_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5165_, 0, v___x_5163_);
        return v___x_5165_;
    } else {
        let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5167_: u8 = 0;
        v___x_5166_ = lean_array_get_size(v_as_5155_);
        v___x_5167_ = lean_nat_dec_le(v_stop_5157_, v___x_5166_);
        if v___x_5167_ == 0 {
            let mut v___x_5168_: u8 = 0;
            v___x_5168_ = lean_nat_dec_lt(v_start_5156_, v___x_5166_);
            if v___x_5168_ == 0 {
                let mut v___x_5169_: *mut LeanObject = core::ptr::null_mut();
                v___x_5169_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5169_, 0, v___x_5163_);
                return v___x_5169_;
            } else {
                let mut v___x_5170_: usize = 0;
                let mut v___x_5171_: usize = 0;
                let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
                v___x_5170_ = lean_usize_of_nat(v_start_5156_);
                v___x_5171_ = lean_usize_of_nat(v___x_5166_);
                v___x_5172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_5155_, v___x_5170_, v___x_5171_, v___x_5163_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
                return v___x_5172_;
            }
        } else {
            let mut v___x_5173_: usize = 0;
            let mut v___x_5174_: usize = 0;
            let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
            v___x_5173_ = lean_usize_of_nat(v_start_5156_);
            v___x_5174_ = lean_usize_of_nat(v_stop_5157_);
            v___x_5175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4_spec__8(v_as_5155_, v___x_5173_, v___x_5174_, v___x_5163_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_);
            return v___x_5175_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4___boxed(
    mut v_as_5176_: *mut LeanObject,
    mut v_start_5177_: *mut LeanObject,
    mut v_stop_5178_: *mut LeanObject,
    mut v___y_5179_: *mut LeanObject,
    mut v___y_5180_: *mut LeanObject,
    mut v___y_5181_: *mut LeanObject,
    mut v___y_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5184_: *mut LeanObject = core::ptr::null_mut();
    v_res_5184_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v_as_5176_, v_start_5177_, v_stop_5178_, v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_);
    lean_dec(v___y_5182_);
    lean_dec_ref(v___y_5181_);
    lean_dec(v___y_5180_);
    lean_dec_ref(v___y_5179_);
    lean_dec(v_stop_5178_);
    lean_dec(v_start_5177_);
    lean_dec_ref(v_as_5176_);
    return v_res_5184_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    v___x_5187_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5187_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2()
-> *mut LeanObject {
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    v___x_5188_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__1);
    v___x_5189_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5189_, 0, v___x_5188_);
    return v___x_5189_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    v___x_5190_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__2);
    v___x_5191_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_5191_, 0, v___x_5190_);
    lean_ctor_set(v___x_5191_, 1, v___x_5190_);
    lean_ctor_set(v___x_5191_, 2, v___x_5190_);
    lean_ctor_set(v___x_5191_, 3, v___x_5190_);
    lean_ctor_set(v___x_5191_, 4, v___x_5190_);
    return v___x_5191_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4()
-> *mut LeanObject {
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    v___x_5192_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_5192_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5()
-> *mut LeanObject {
    let mut v___x_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: *mut LeanObject = core::ptr::null_mut();
    v___x_5193_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__4);
    v___x_5194_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5194_, 0, v___x_5193_);
    return v___x_5194_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6()
-> *mut LeanObject {
    let mut v___x_5195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    v___x_5195_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__5);
    v___x_5196_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5196_, 0, v___x_5195_);
    lean_ctor_set(v___x_5196_, 1, v___x_5195_);
    return v___x_5196_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(
    mut v_s_5197_: *mut LeanObject,
    mut v___f_5198_: *mut LeanObject,
    mut v___x_5199_: u8,
    mut v___y_5200_: *mut LeanObject,
    mut v___y_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
    mut v___y_5203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5221_: u8 = 0;
    let mut v_a_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5229_: u8 = 0;
    let mut v___y_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: u8 = 0;
    let mut v___y_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5253_: u8 = 0;
    let mut v___x_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_5255_: u8 = 0;
    let mut v_ctxApprox_5256_: u8 = 0;
    let mut v_quasiPatternApprox_5257_: u8 = 0;
    let mut v_constApprox_5258_: u8 = 0;
    let mut v_isDefEqStuckEx_5259_: u8 = 0;
    let mut v_unificationHints_5260_: u8 = 0;
    let mut v_proofIrrelevance_5261_: u8 = 0;
    let mut v_assignSyntheticOpaque_5262_: u8 = 0;
    let mut v_offsetCnstrs_5263_: u8 = 0;
    let mut v_etaStruct_5264_: u8 = 0;
    let mut v_univApprox_5265_: u8 = 0;
    let mut v_iota_5266_: u8 = 0;
    let mut v_beta_5267_: u8 = 0;
    let mut v_proj_5268_: u8 = 0;
    let mut v_zeta_5269_: u8 = 0;
    let mut v_zetaDelta_5270_: u8 = 0;
    let mut v_zetaUnused_5271_: u8 = 0;
    let mut v_zetaHave_5272_: u8 = 0;
    let mut v___x_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5275_: u8 = 0;
    let mut v_trackZetaDelta_5276_: u8 = 0;
    let mut v_zetaDeltaSet_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5283_: u8 = 0;
    let mut v_inTypeClassResolution_5284_: u8 = 0;
    let mut v_cacheInferType_5285_: u8 = 0;
    let mut v_config_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: u64 = 0;
    let mut v___x_5289_: u64 = 0;
    let mut v___x_5290_: u64 = 0;
    let mut v___x_5291_: u64 = 0;
    let mut v___x_5292_: u64 = 0;
    let mut v_key_5293_: u64 = 0;
    let mut v___x_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unfoldCounter_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: u8 = 0;
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: u8 = 0;
    let mut v_a_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5312_: u8 = 0;
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5316_: u8 = 0;
    let mut v_reuseFailAlloc_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5318_: u8 = 0;
    let mut v___y_5320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_5323_: u8 = 0;
    let mut v___x_5324_: u8 = 0;
    let mut v___x_5325_: u8 = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5339_: u8 = 0;
    let mut v_inheritedTraceOptions_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: u8 = 0;
    let mut v_fileName_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5357_: u8 = 0;
    let mut v_inheritedTraceOptions_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: u8 = 0;
    let mut v___x_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5373_: u8 = 0;
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5379_: u8 = 0;
    let mut v_unused_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5384_: u8 = 0;
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5388_: u8 = 0;
    let mut v___y_5390_: u8 = 0;
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5402_: u8 = 0;
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut v_unused_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5326_ = lean_st_ref_get(v___y_5203_);
                v_fileName_5327_ = lean_ctor_get(v___y_5202_, 0);
                v_fileMap_5328_ = lean_ctor_get(v___y_5202_, 1);
                v_options_5329_ = lean_ctor_get(v___y_5202_, 2);
                v_currRecDepth_5330_ = lean_ctor_get(v___y_5202_, 3);
                v_ref_5331_ = lean_ctor_get(v___y_5202_, 5);
                v_currNamespace_5332_ = lean_ctor_get(v___y_5202_, 6);
                v_openDecls_5333_ = lean_ctor_get(v___y_5202_, 7);
                v_initHeartbeats_5334_ = lean_ctor_get(v___y_5202_, 8);
                v_maxHeartbeats_5335_ = lean_ctor_get(v___y_5202_, 9);
                v_quotContext_5336_ = lean_ctor_get(v___y_5202_, 10);
                v_currMacroScope_5337_ = lean_ctor_get(v___y_5202_, 11);
                v_cancelTk_x3f_5338_ = lean_ctor_get(v___y_5202_, 12);
                v_suppressElabErrors_5339_ = lean_ctor_get_uint8(
                    v___y_5202_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_5340_ = lean_ctor_get(v___y_5202_, 13);
                v_env_5341_ = lean_ctor_get(v___x_5326_, 0);
                lean_inc_ref(v_env_5341_);
                lean_dec(v___x_5326_);
                v___x_5342_ = l_Lean_diagnostics;
                lean_inc_ref(v_options_5329_);
                v___x_5343_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_5329_, v___x_5342_, v___x_5199_);
                v___x_5344_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_5343_, v___x_5342_);
                v___x_5411_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_5341_);
                lean_dec_ref(v_env_5341_);
                if v___x_5411_ == 0 {
                    if v___x_5344_ == 0 {
                        v_fileName_5346_ = v_fileName_5327_;
                        v_fileMap_5347_ = v_fileMap_5328_;
                        v_currRecDepth_5348_ = v_currRecDepth_5330_;
                        v_ref_5349_ = v_ref_5331_;
                        v_currNamespace_5350_ = v_currNamespace_5332_;
                        v_openDecls_5351_ = v_openDecls_5333_;
                        v_initHeartbeats_5352_ = v_initHeartbeats_5334_;
                        v_maxHeartbeats_5353_ = v_maxHeartbeats_5335_;
                        v_quotContext_5354_ = v_quotContext_5336_;
                        v_currMacroScope_5355_ = v_currMacroScope_5337_;
                        v_cancelTk_x3f_5356_ = v_cancelTk_x3f_5338_;
                        v_suppressElabErrors_5357_ = v_suppressElabErrors_5339_;
                        v_inheritedTraceOptions_5358_ = v_inheritedTraceOptions_5340_;
                        v___y_5359_ = v___y_5203_;
                        state = 14;
                        continue;
                    } else {
                        v___y_5390_ = v___x_5411_;
                        state = 19;
                        continue;
                    }
                } else {
                    v___y_5390_ = v___x_5344_;
                    state = 19;
                    continue;
                }
            }
            1 => {
                v___x_5211_ = lean_array_get_size(v___y_5210_);
                v___x_5212_ = l_Array_filterMapM___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__4(v___y_5210_, v___y_5207_, v___x_5211_, v___y_5200_, v___y_5201_, v___y_5206_, v___y_5209_);
                lean_dec_ref(v___y_5206_);
                lean_dec(v___y_5207_);
                lean_dec_ref(v___y_5210_);
                if lean_obj_tag(v___x_5212_) == 0 {
                    v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
                    v_isSharedCheck_5221_ = (!lean_is_exclusive(v___x_5212_)) as u8;
                    if v_isSharedCheck_5221_ == 0 {
                        v___x_5215_ = v___x_5212_;
                        v_isShared_5216_ = v_isSharedCheck_5221_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5213_);
                        lean_dec(v___x_5212_);
                        v___x_5215_ = lean_box(0);
                        v_isShared_5216_ = v_isSharedCheck_5221_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_5208_);
                    v_a_5222_ = lean_ctor_get(v___x_5212_, 0);
                    v_isSharedCheck_5229_ = (!lean_is_exclusive(v___x_5212_)) as u8;
                    if v_isSharedCheck_5229_ == 0 {
                        v___x_5224_ = v___x_5212_;
                        v_isShared_5225_ = v_isSharedCheck_5229_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5222_);
                        lean_dec(v___x_5212_);
                        v___x_5224_ = lean_box(0);
                        v_isShared_5225_ = v_isSharedCheck_5229_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5217_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5217_, 0, v___y_5208_);
                lean_ctor_set(v___x_5217_, 1, v_a_5213_);
                if v_isShared_5216_ == 0 {
                    lean_ctor_set(v___x_5215_, 0, v___x_5217_);
                    v___x_5219_ = v___x_5215_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5220_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5220_, 0, v___x_5217_);
                    v___x_5219_ = v_reuseFailAlloc_5220_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5219_;
            }
            4 => {
                if v_isShared_5225_ == 0 {
                    v___x_5227_ = v___x_5224_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
                    v___x_5227_ = v_reuseFailAlloc_5228_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5227_;
            }
            6 => {
                v___x_5239_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v___y_5236_, v___y_5232_, v___y_5235_, v___y_5238_);
                lean_dec(v___y_5238_);
                lean_dec(v___y_5236_);
                v___y_5206_ = v___y_5231_;
                v___y_5207_ = v___y_5233_;
                v___y_5208_ = v___y_5234_;
                v___y_5209_ = v___y_5237_;
                v___y_5210_ = v___x_5239_;
                state = 1;
                continue;
            }
            7 => {
                v___x_5249_ = lean_nat_dec_le(v___y_5248_, v___y_5247_);
                if v___x_5249_ == 0 {
                    lean_dec(v___y_5247_);
                    lean_inc(v___y_5248_);
                    v___y_5231_ = v___y_5242_;
                    v___y_5232_ = v___y_5241_;
                    v___y_5233_ = v___y_5243_;
                    v___y_5234_ = v___y_5244_;
                    v___y_5235_ = v___y_5248_;
                    v___y_5236_ = v___y_5245_;
                    v___y_5237_ = v___y_5246_;
                    v___y_5238_ = v___y_5248_;
                    state = 6;
                    continue;
                } else {
                    v___y_5231_ = v___y_5242_;
                    v___y_5232_ = v___y_5241_;
                    v___y_5233_ = v___y_5243_;
                    v___y_5234_ = v___y_5244_;
                    v___y_5235_ = v___y_5248_;
                    v___y_5236_ = v___y_5245_;
                    v___y_5237_ = v___y_5246_;
                    v___y_5238_ = v___y_5247_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_5254_ = l_Lean_Meta_Context_config(v___y_5200_);
                v_foApprox_5255_ = lean_ctor_get_uint8(v___x_5254_, 0 as u32);
                v_ctxApprox_5256_ = lean_ctor_get_uint8(v___x_5254_, 1 as u32);
                v_quasiPatternApprox_5257_ = lean_ctor_get_uint8(v___x_5254_, 2 as u32);
                v_constApprox_5258_ = lean_ctor_get_uint8(v___x_5254_, 3 as u32);
                v_isDefEqStuckEx_5259_ = lean_ctor_get_uint8(v___x_5254_, 4 as u32);
                v_unificationHints_5260_ = lean_ctor_get_uint8(v___x_5254_, 5 as u32);
                v_proofIrrelevance_5261_ = lean_ctor_get_uint8(v___x_5254_, 6 as u32);
                v_assignSyntheticOpaque_5262_ = lean_ctor_get_uint8(v___x_5254_, 7 as u32);
                v_offsetCnstrs_5263_ = lean_ctor_get_uint8(v___x_5254_, 8 as u32);
                v_etaStruct_5264_ = lean_ctor_get_uint8(v___x_5254_, 10 as u32);
                v_univApprox_5265_ = lean_ctor_get_uint8(v___x_5254_, 11 as u32);
                v_iota_5266_ = lean_ctor_get_uint8(v___x_5254_, 12 as u32);
                v_beta_5267_ = lean_ctor_get_uint8(v___x_5254_, 13 as u32);
                v_proj_5268_ = lean_ctor_get_uint8(v___x_5254_, 14 as u32);
                v_zeta_5269_ = lean_ctor_get_uint8(v___x_5254_, 15 as u32);
                v_zetaDelta_5270_ = lean_ctor_get_uint8(v___x_5254_, 16 as u32);
                v_zetaUnused_5271_ = lean_ctor_get_uint8(v___x_5254_, 17 as u32);
                v_zetaHave_5272_ = lean_ctor_get_uint8(v___x_5254_, 18 as u32);
                v_isSharedCheck_5318_ = (!lean_is_exclusive(v___x_5254_)) as u8;
                if v_isSharedCheck_5318_ == 0 {
                    v___x_5274_ = v___x_5254_;
                    v_isShared_5275_ = v_isSharedCheck_5318_;
                    state = 9;
                    continue;
                } else {
                    lean_dec(v___x_5254_);
                    v___x_5274_ = lean_box(0);
                    v_isShared_5275_ = v_isSharedCheck_5318_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_trackZetaDelta_5276_ = lean_ctor_get_uint8(
                    v___y_5200_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5277_ = lean_ctor_get(v___y_5200_, 1);
                v_lctx_5278_ = lean_ctor_get(v___y_5200_, 2);
                v_localInstances_5279_ = lean_ctor_get(v___y_5200_, 3);
                v_defEqCtx_x3f_5280_ = lean_ctor_get(v___y_5200_, 4);
                v_synthPendingDepth_5281_ = lean_ctor_get(v___y_5200_, 5);
                v_canUnfold_x3f_5282_ = lean_ctor_get(v___y_5200_, 6);
                v_univApprox_5283_ = lean_ctor_get_uint8(
                    v___y_5200_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5284_ = lean_ctor_get_uint8(
                    v___y_5200_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5285_ = lean_ctor_get_uint8(
                    v___y_5200_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_5275_ == 0 {
                    v_config_5287_ = v___x_5274_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5317_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 0 as u32, v_foApprox_5255_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 1 as u32, v_ctxApprox_5256_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5317_,
                        2 as u32,
                        v_quasiPatternApprox_5257_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 3 as u32, v_constApprox_5258_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 4 as u32, v_isDefEqStuckEx_5259_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 5 as u32, v_unificationHints_5260_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 6 as u32, v_proofIrrelevance_5261_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5317_,
                        7 as u32,
                        v_assignSyntheticOpaque_5262_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 8 as u32, v_offsetCnstrs_5263_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 10 as u32, v_etaStruct_5264_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 11 as u32, v_univApprox_5265_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 12 as u32, v_iota_5266_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 13 as u32, v_beta_5267_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 14 as u32, v_proj_5268_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 15 as u32, v_zeta_5269_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 16 as u32, v_zetaDelta_5270_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 17 as u32, v_zetaUnused_5271_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5317_, 18 as u32, v_zetaHave_5272_);
                    v_config_5287_ = v_reuseFailAlloc_5317_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                lean_ctor_set_uint8(v_config_5287_, 9 as u32, v___y_5253_);
                v___x_5288_ = l_Lean_Meta_Context_configKey(v___y_5200_);
                v___x_5289_ = 3u64;
                v___x_5290_ = lean_uint64_shift_right(v___x_5288_, v___x_5289_);
                v___x_5291_ = lean_uint64_shift_left(v___x_5290_, v___x_5289_);
                v___x_5292_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_5253_);
                v_key_5293_ = lean_uint64_lor(v___x_5291_, v___x_5292_);
                v___x_5294_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5294_, 0, v_config_5287_);
                lean_ctor_set_uint64(
                    v___x_5294_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_5293_,
                );
                lean_inc(v_canUnfold_x3f_5282_);
                lean_inc(v_synthPendingDepth_5281_);
                lean_inc(v_defEqCtx_x3f_5280_);
                lean_inc_ref(v_localInstances_5279_);
                lean_inc_ref(v_lctx_5278_);
                lean_inc(v_zetaDeltaSet_5277_);
                v___x_5295_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5295_, 0, v___x_5294_);
                lean_ctor_set(v___x_5295_, 1, v_zetaDeltaSet_5277_);
                lean_ctor_set(v___x_5295_, 2, v_lctx_5278_);
                lean_ctor_set(v___x_5295_, 3, v_localInstances_5279_);
                lean_ctor_set(v___x_5295_, 4, v_defEqCtx_x3f_5280_);
                lean_ctor_set(v___x_5295_, 5, v_synthPendingDepth_5281_);
                lean_ctor_set(v___x_5295_, 6, v_canUnfold_x3f_5282_);
                lean_ctor_set_uint8(
                    v___x_5295_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5276_,
                );
                lean_ctor_set_uint8(
                    v___x_5295_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5283_,
                );
                lean_ctor_set_uint8(
                    v___x_5295_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5284_,
                );
                lean_ctor_set_uint8(
                    v___x_5295_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5285_,
                );
                lean_inc_ref(v___y_5251_);
                v___x_5296_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure(v_s_5197_, v___x_5295_, v___y_5201_, v___y_5251_, v___y_5252_);
                lean_dec_ref_known(v___x_5295_, 7);
                if lean_obj_tag(v___x_5296_) == 0 {
                    v_a_5297_ = lean_ctor_get(v___x_5296_, 0);
                    lean_inc(v_a_5297_);
                    lean_dec_ref_known(v___x_5296_, 1);
                    v___x_5298_ = lean_st_ref_get(v___y_5201_);
                    v_diag_5299_ = lean_ctor_get(v___x_5298_, 4);
                    lean_inc_ref(v_diag_5299_);
                    lean_dec(v___x_5298_);
                    v_unfoldCounter_5300_ = lean_ctor_get(v_diag_5299_, 0);
                    lean_inc_ref(v_unfoldCounter_5300_);
                    lean_dec_ref(v_diag_5299_);
                    v___x_5301_ = lean_unsigned_to_nat(0);
                    v___x_5302_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0;
                    v___x_5303_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_unfoldCounter_5300_, v___f_5198_, v___x_5302_);
                    lean_dec_ref(v_unfoldCounter_5300_);
                    v___x_5304_ = lean_array_get_size(v___x_5303_);
                    v___x_5305_ = lean_nat_dec_eq(v___x_5304_, v___x_5301_);
                    if v___x_5305_ == 0 {
                        v___x_5306_ = lean_unsigned_to_nat(1);
                        v___x_5307_ = lean_nat_sub(v___x_5304_, v___x_5306_);
                        v___x_5308_ = lean_nat_dec_le(v___x_5301_, v___x_5307_);
                        if v___x_5308_ == 0 {
                            lean_inc(v___x_5307_);
                            v___y_5241_ = v___x_5303_;
                            v___y_5242_ = v___y_5251_;
                            v___y_5243_ = v___x_5301_;
                            v___y_5244_ = v_a_5297_;
                            v___y_5245_ = v___x_5304_;
                            v___y_5246_ = v___y_5252_;
                            v___y_5247_ = v___x_5307_;
                            v___y_5248_ = v___x_5307_;
                            state = 7;
                            continue;
                        } else {
                            v___y_5241_ = v___x_5303_;
                            v___y_5242_ = v___y_5251_;
                            v___y_5243_ = v___x_5301_;
                            v___y_5244_ = v_a_5297_;
                            v___y_5245_ = v___x_5304_;
                            v___y_5246_ = v___y_5252_;
                            v___y_5247_ = v___x_5307_;
                            v___y_5248_ = v___x_5301_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___y_5206_ = v___y_5251_;
                        v___y_5207_ = v___x_5301_;
                        v___y_5208_ = v_a_5297_;
                        v___y_5209_ = v___y_5252_;
                        v___y_5210_ = v___x_5303_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_5251_);
                    lean_dec_ref(v___f_5198_);
                    v_a_5309_ = lean_ctor_get(v___x_5296_, 0);
                    v_isSharedCheck_5316_ = (!lean_is_exclusive(v___x_5296_)) as u8;
                    if v_isSharedCheck_5316_ == 0 {
                        v___x_5311_ = v___x_5296_;
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_5309_);
                        lean_dec(v___x_5296_);
                        v___x_5311_ = lean_box(0);
                        v_isShared_5312_ = v_isSharedCheck_5316_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_5312_ == 0 {
                    v___x_5314_ = v___x_5311_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5315_, 0, v_a_5309_);
                    v___x_5314_ = v_reuseFailAlloc_5315_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5314_;
            }
            13 => {
                v___x_5322_ = l_Lean_Meta_Context_config(v___y_5200_);
                v_transparency_5323_ = lean_ctor_get_uint8(v___x_5322_, 9 as u32);
                lean_dec_ref(v___x_5322_);
                v___x_5324_ = 1;
                v___x_5325_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_5323_, v___x_5324_);
                if v___x_5325_ == 0 {
                    v___y_5251_ = v___y_5320_;
                    v___y_5252_ = v___y_5321_;
                    v___y_5253_ = v_transparency_5323_;
                    state = 8;
                    continue;
                } else {
                    v___y_5251_ = v___y_5320_;
                    v___y_5252_ = v___y_5321_;
                    v___y_5253_ = v___x_5324_;
                    state = 8;
                    continue;
                }
            }
            14 => {
                v___x_5360_ = l_Lean_maxRecDepth;
                v___x_5361_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_5343_, v___x_5360_);
                lean_inc_ref(v_inheritedTraceOptions_5358_);
                lean_inc(v_cancelTk_x3f_5356_);
                lean_inc(v_currMacroScope_5355_);
                lean_inc(v_quotContext_5354_);
                lean_inc(v_maxHeartbeats_5353_);
                lean_inc(v_initHeartbeats_5352_);
                lean_inc(v_openDecls_5351_);
                lean_inc(v_currNamespace_5350_);
                lean_inc(v_ref_5349_);
                lean_inc(v_currRecDepth_5348_);
                lean_inc_ref(v_fileMap_5347_);
                lean_inc_ref(v_fileName_5346_);
                v___x_5362_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_5362_, 0, v_fileName_5346_);
                lean_ctor_set(v___x_5362_, 1, v_fileMap_5347_);
                lean_ctor_set(v___x_5362_, 2, v___x_5343_);
                lean_ctor_set(v___x_5362_, 3, v_currRecDepth_5348_);
                lean_ctor_set(v___x_5362_, 4, v___x_5361_);
                lean_ctor_set(v___x_5362_, 5, v_ref_5349_);
                lean_ctor_set(v___x_5362_, 6, v_currNamespace_5350_);
                lean_ctor_set(v___x_5362_, 7, v_openDecls_5351_);
                lean_ctor_set(v___x_5362_, 8, v_initHeartbeats_5352_);
                lean_ctor_set(v___x_5362_, 9, v_maxHeartbeats_5353_);
                lean_ctor_set(v___x_5362_, 10, v_quotContext_5354_);
                lean_ctor_set(v___x_5362_, 11, v_currMacroScope_5355_);
                lean_ctor_set(v___x_5362_, 12, v_cancelTk_x3f_5356_);
                lean_ctor_set(v___x_5362_, 13, v_inheritedTraceOptions_5358_);
                lean_ctor_set_uint8(
                    v___x_5362_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_5344_,
                );
                lean_ctor_set_uint8(
                    v___x_5362_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_5357_,
                );
                v___x_5363_ = l_Lean_isDiagnosticsEnabled___redArg(v___x_5362_);
                if lean_obj_tag(v___x_5363_) == 0 {
                    v_a_5364_ = lean_ctor_get(v___x_5363_, 0);
                    lean_inc(v_a_5364_);
                    lean_dec_ref_known(v___x_5363_, 1);
                    v___x_5365_ = (lean_unbox(v_a_5364_) as u8);
                    lean_dec(v_a_5364_);
                    if v___x_5365_ == 0 {
                        v___y_5320_ = v___x_5362_;
                        v___y_5321_ = v___y_5359_;
                        state = 13;
                        continue;
                    } else {
                        v___x_5366_ = lean_st_ref_take(v___y_5201_);
                        v_mctx_5367_ = lean_ctor_get(v___x_5366_, 0);
                        v_cache_5368_ = lean_ctor_get(v___x_5366_, 1);
                        v_zetaDeltaFVarIds_5369_ = lean_ctor_get(v___x_5366_, 2);
                        v_postponed_5370_ = lean_ctor_get(v___x_5366_, 3);
                        v_isSharedCheck_5379_ = (!lean_is_exclusive(v___x_5366_)) as u8;
                        if v_isSharedCheck_5379_ == 0 {
                            v_unused_5380_ = lean_ctor_get(v___x_5366_, 4);
                            lean_dec(v_unused_5380_);
                            v___x_5372_ = v___x_5366_;
                            v_isShared_5373_ = v_isSharedCheck_5379_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_postponed_5370_);
                            lean_inc(v_zetaDeltaFVarIds_5369_);
                            lean_inc(v_cache_5368_);
                            lean_inc(v_mctx_5367_);
                            lean_dec(v___x_5366_);
                            v___x_5372_ = lean_box(0);
                            v_isShared_5373_ = v_isSharedCheck_5379_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_5362_, 14);
                    lean_dec_ref(v___f_5198_);
                    lean_dec_ref(v_s_5197_);
                    v_a_5381_ = lean_ctor_get(v___x_5363_, 0);
                    v_isSharedCheck_5388_ = (!lean_is_exclusive(v___x_5363_)) as u8;
                    if v_isSharedCheck_5388_ == 0 {
                        v___x_5383_ = v___x_5363_;
                        v_isShared_5384_ = v_isSharedCheck_5388_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5381_);
                        lean_dec(v___x_5363_);
                        v___x_5383_ = lean_box(0);
                        v_isShared_5384_ = v_isSharedCheck_5388_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                v___x_5374_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__3);
                if v_isShared_5373_ == 0 {
                    lean_ctor_set(v___x_5372_, 4, v___x_5374_);
                    v___x_5376_ = v___x_5372_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 0, v_mctx_5367_);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 1, v_cache_5368_);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 2, v_zetaDeltaFVarIds_5369_);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 3, v_postponed_5370_);
                    lean_ctor_set(v_reuseFailAlloc_5378_, 4, v___x_5374_);
                    v___x_5376_ = v_reuseFailAlloc_5378_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_5377_ = lean_st_ref_set(v___y_5201_, v___x_5376_);
                v___y_5320_ = v___x_5362_;
                v___y_5321_ = v___y_5359_;
                state = 13;
                continue;
            }
            17 => {
                if v_isShared_5384_ == 0 {
                    v___x_5386_ = v___x_5383_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5387_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_a_5381_);
                    v___x_5386_ = v_reuseFailAlloc_5387_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5386_;
            }
            19 => {
                if v___y_5390_ == 0 {
                    v___x_5391_ = lean_st_ref_take(v___y_5203_);
                    v_env_5392_ = lean_ctor_get(v___x_5391_, 0);
                    v_nextMacroScope_5393_ = lean_ctor_get(v___x_5391_, 1);
                    v_ngen_5394_ = lean_ctor_get(v___x_5391_, 2);
                    v_auxDeclNGen_5395_ = lean_ctor_get(v___x_5391_, 3);
                    v_traceState_5396_ = lean_ctor_get(v___x_5391_, 4);
                    v_messages_5397_ = lean_ctor_get(v___x_5391_, 6);
                    v_infoState_5398_ = lean_ctor_get(v___x_5391_, 7);
                    v_snapshotTasks_5399_ = lean_ctor_get(v___x_5391_, 8);
                    v_isSharedCheck_5409_ = (!lean_is_exclusive(v___x_5391_)) as u8;
                    if v_isSharedCheck_5409_ == 0 {
                        v_unused_5410_ = lean_ctor_get(v___x_5391_, 5);
                        lean_dec(v_unused_5410_);
                        v___x_5401_ = v___x_5391_;
                        v_isShared_5402_ = v_isSharedCheck_5409_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_5399_);
                        lean_inc(v_infoState_5398_);
                        lean_inc(v_messages_5397_);
                        lean_inc(v_traceState_5396_);
                        lean_inc(v_auxDeclNGen_5395_);
                        lean_inc(v_ngen_5394_);
                        lean_inc(v_nextMacroScope_5393_);
                        lean_inc(v_env_5392_);
                        lean_dec(v___x_5391_);
                        v___x_5401_ = lean_box(0);
                        v_isShared_5402_ = v_isSharedCheck_5409_;
                        state = 20;
                        continue;
                    }
                } else {
                    v_fileName_5346_ = v_fileName_5327_;
                    v_fileMap_5347_ = v_fileMap_5328_;
                    v_currRecDepth_5348_ = v_currRecDepth_5330_;
                    v_ref_5349_ = v_ref_5331_;
                    v_currNamespace_5350_ = v_currNamespace_5332_;
                    v_openDecls_5351_ = v_openDecls_5333_;
                    v_initHeartbeats_5352_ = v_initHeartbeats_5334_;
                    v_maxHeartbeats_5353_ = v_maxHeartbeats_5335_;
                    v_quotContext_5354_ = v_quotContext_5336_;
                    v_currMacroScope_5355_ = v_currMacroScope_5337_;
                    v_cancelTk_x3f_5356_ = v_cancelTk_x3f_5338_;
                    v_suppressElabErrors_5357_ = v_suppressElabErrors_5339_;
                    v_inheritedTraceOptions_5358_ = v_inheritedTraceOptions_5340_;
                    v___y_5359_ = v___y_5203_;
                    state = 14;
                    continue;
                }
            }
            20 => {
                v___x_5403_ = l_Lean_Kernel_enableDiag(v_env_5392_, v___x_5344_);
                v___x_5404_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
                if v_isShared_5402_ == 0 {
                    lean_ctor_set(v___x_5401_, 5, v___x_5404_);
                    lean_ctor_set(v___x_5401_, 0, v___x_5403_);
                    v___x_5406_ = v___x_5401_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5408_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 0, v___x_5403_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 1, v_nextMacroScope_5393_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 2, v_ngen_5394_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 3, v_auxDeclNGen_5395_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 4, v_traceState_5396_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 5, v___x_5404_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 6, v_messages_5397_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 7, v_infoState_5398_);
                    lean_ctor_set(v_reuseFailAlloc_5408_, 8, v_snapshotTasks_5399_);
                    v___x_5406_ = v_reuseFailAlloc_5408_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_5407_ = lean_st_ref_set(v___y_5203_, v___x_5406_);
                v_fileName_5346_ = v_fileName_5327_;
                v_fileMap_5347_ = v_fileMap_5328_;
                v_currRecDepth_5348_ = v_currRecDepth_5330_;
                v_ref_5349_ = v_ref_5331_;
                v_currNamespace_5350_ = v_currNamespace_5332_;
                v_openDecls_5351_ = v_openDecls_5333_;
                v_initHeartbeats_5352_ = v_initHeartbeats_5334_;
                v_maxHeartbeats_5353_ = v_maxHeartbeats_5335_;
                v_quotContext_5354_ = v_quotContext_5336_;
                v_currMacroScope_5355_ = v_currMacroScope_5337_;
                v_cancelTk_x3f_5356_ = v_cancelTk_x3f_5338_;
                v_suppressElabErrors_5357_ = v_suppressElabErrors_5339_;
                v_inheritedTraceOptions_5358_ = v_inheritedTraceOptions_5340_;
                v___y_5359_ = v___y_5203_;
                state = 14;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed(
    mut v_s_5412_: *mut LeanObject,
    mut v___f_5413_: *mut LeanObject,
    mut v___x_5414_: *mut LeanObject,
    mut v___y_5415_: *mut LeanObject,
    mut v___y_5416_: *mut LeanObject,
    mut v___y_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_13211__boxed_5420_: u8 = 0;
    let mut v_res_5421_: *mut LeanObject = core::ptr::null_mut();
    v___x_13211__boxed_5420_ = (lean_unbox(v___x_5414_) as u8);
    v_res_5421_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1(
            v_s_5412_,
            v___f_5413_,
            v___x_13211__boxed_5420_,
            v___y_5415_,
            v___y_5416_,
            v___y_5417_,
            v___y_5418_,
        );
    lean_dec(v___y_5418_);
    lean_dec_ref(v___y_5417_);
    lean_dec(v___y_5416_);
    lean_dec_ref(v___y_5415_);
    return v_res_5421_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2()
-> *mut LeanObject {
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    v___x_5424_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__1;
    v___x_5425_ = l_Lean_stringToMessageData(v___x_5424_);
    return v___x_5425_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4()
-> *mut LeanObject {
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    v___x_5427_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__3;
    v___x_5428_ = l_Lean_stringToMessageData(v___x_5427_);
    return v___x_5428_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6()
-> *mut LeanObject {
    let mut v___x_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    v___x_5430_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__5;
    v___x_5431_ = l_Lean_stringToMessageData(v___x_5430_);
    return v___x_5431_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8()
-> *mut LeanObject {
    let mut v___x_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    v___x_5433_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__7;
    v___x_5434_ = l_Lean_stringToMessageData(v___x_5433_);
    return v___x_5434_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10()
-> *mut LeanObject {
    let mut v___x_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    v___x_5436_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__9;
    v___x_5437_ = l_Lean_stringToMessageData(v___x_5436_);
    return v___x_5437_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12()
-> *mut LeanObject {
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    v___x_5439_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__11;
    v___x_5440_ = l_Lean_stringToMessageData(v___x_5439_);
    return v___x_5440_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19()
-> *mut LeanObject {
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    v___x_5451_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__18;
    v___x_5452_ = l_Lean_stringToMessageData(v___x_5451_);
    return v___x_5452_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21()
-> *mut LeanObject {
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    v___x_5454_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__20;
    v___x_5455_ = l_Lean_stringToMessageData(v___x_5454_);
    return v___x_5455_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23()
-> *mut LeanObject {
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    v___x_5457_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__22;
    v___x_5458_ = l_Lean_stringToMessageData(v___x_5457_);
    return v___x_5458_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25()
-> *mut LeanObject {
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5461_: *mut LeanObject = core::ptr::null_mut();
    v___x_5460_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__24;
    v___x_5461_ = l_Lean_stringToMessageData(v___x_5460_);
    return v___x_5461_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29()
-> *mut LeanObject {
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    v___x_5467_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__28;
    v___x_5468_ = l_Lean_stringToMessageData(v___x_5467_);
    return v___x_5468_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31()
-> *mut LeanObject {
    let mut v___x_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    v___x_5470_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__30;
    v___x_5471_ = l_Lean_stringToMessageData(v___x_5470_);
    return v___x_5471_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33()
-> *mut LeanObject {
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    v___x_5473_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__32;
    v___x_5474_ = l_Lean_stringToMessageData(v___x_5473_);
    return v___x_5474_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39()
-> *mut LeanObject {
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    v___x_5482_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__38;
    v___x_5483_ = l_Lean_stringToMessageData(v___x_5482_);
    return v___x_5483_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41()
-> *mut LeanObject {
    let mut v___x_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    v___x_5485_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__40;
    v___x_5486_ = l_Lean_stringToMessageData(v___x_5485_);
    return v___x_5486_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43()
-> *mut LeanObject {
    let mut v___x_5488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut LeanObject = core::ptr::null_mut();
    v___x_5488_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__42;
    v___x_5489_ = l_Lean_stringToMessageData(v___x_5488_);
    return v___x_5489_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45()
-> *mut LeanObject {
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    v___x_5491_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__44;
    v___x_5492_ = l_Lean_stringToMessageData(v___x_5491_);
    return v___x_5492_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49()
-> *mut LeanObject {
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    v___x_5496_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__48;
    v___x_5497_ = l_Lean_stringToMessageData(v___x_5496_);
    return v___x_5497_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51()
-> *mut LeanObject {
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    v___x_5499_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__50;
    v___x_5500_ = l_Lean_stringToMessageData(v___x_5499_);
    return v___x_5500_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(
    mut v_tacticName_5501_: *mut LeanObject,
    mut v_expectedType_5502_: *mut LeanObject,
    mut v_s_5503_: *mut LeanObject,
    mut v_r_5504_: *mut LeanObject,
    mut v_a_5505_: *mut LeanObject,
    mut v_a_5506_: *mut LeanObject,
    mut v_a_5507_: *mut LeanObject,
    mut v_a_5508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: u8 = 0;
    let mut v___f_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: u8 = 0;
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5520_: u8 = 0;
    let mut v___y_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5560_: u8 = 0;
    let mut v___y_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: u8 = 0;
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: u8 = 0;
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: u8 = 0;
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: u8 = 0;
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5647_: u8 = 0;
    let mut v_isSharedCheck_5648_: u8 = 0;
    let mut v_a_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5652_: u8 = 0;
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5656_: u8 = 0;
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5510_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__7;
                v___x_5511_ = l_Lean_Expr_isAppOf(v_r_5504_, v___x_5510_);
                if v___x_5511_ == 0 {
                    v___f_5512_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__0;
                    v___x_5513_ = 1;
                    v___x_5514_ = lean_box((v___x_5513_) as usize);
                    lean_inc_ref(v_s_5503_);
                    v___f_5515_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___boxed as *mut core::ffi::c_void, 8, 3);
                    lean_closure_set(v___f_5515_, 0, v_s_5503_);
                    lean_closure_set(v___f_5515_, 1, v___f_5512_);
                    lean_closure_set(v___f_5515_, 2, v___x_5514_);
                    v___x_5516_ = l_Lean_withoutModifyingState___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__6___redArg(v___f_5515_, v_a_5505_, v_a_5506_, v_a_5507_, v_a_5508_);
                    if lean_obj_tag(v___x_5516_) == 0 {
                        v_a_5517_ = lean_ctor_get(v___x_5516_, 0);
                        v_isSharedCheck_5648_ = (!lean_is_exclusive(v___x_5516_)) as u8;
                        if v_isSharedCheck_5648_ == 0 {
                            v___x_5519_ = v___x_5516_;
                            v_isShared_5520_ = v_isSharedCheck_5648_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5517_);
                            lean_dec(v___x_5516_);
                            v___x_5519_ = lean_box(0);
                            v_isShared_5520_ = v_isSharedCheck_5648_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_s_5503_);
                        lean_dec_ref(v_expectedType_5502_);
                        lean_dec(v_tacticName_5501_);
                        v_a_5649_ = lean_ctor_get(v___x_5516_, 0);
                        v_isSharedCheck_5656_ = (!lean_is_exclusive(v___x_5516_)) as u8;
                        if v_isSharedCheck_5656_ == 0 {
                            v___x_5651_ = v___x_5516_;
                            v_isShared_5652_ = v_isSharedCheck_5656_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5649_);
                            lean_dec(v___x_5516_);
                            v___x_5651_ = lean_box(0);
                            v_isShared_5652_ = v_isSharedCheck_5656_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_s_5503_);
                    v___x_5657_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once
                        ),
                        _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4,
                    );
                    v___x_5658_ = l_Lean_MessageData_ofName(v_tacticName_5501_);
                    v___x_5659_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5659_, 0, v___x_5657_);
                    lean_ctor_set(v___x_5659_, 1, v___x_5658_);
                    v___x_5660_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__51);
                    v___x_5661_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5661_, 0, v___x_5659_);
                    lean_ctor_set(v___x_5661_, 1, v___x_5660_);
                    v___x_5662_ = l_Lean_indentExpr(v_expectedType_5502_);
                    v___x_5663_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5663_, 0, v___x_5661_);
                    lean_ctor_set(v___x_5663_, 1, v___x_5662_);
                    v___x_5664_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8_once
                        ),
                        _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__8,
                    );
                    v___x_5665_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5665_, 0, v___x_5663_);
                    lean_ctor_set(v___x_5665_, 1, v___x_5664_);
                    v___x_5666_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5666_, 0, v___x_5665_);
                    return v___x_5666_;
                }
            }
            1 => {
                v_fst_5556_ = lean_ctor_get(v_a_5517_, 0);
                v_snd_5557_ = lean_ctor_get(v_a_5517_, 1);
                v_isSharedCheck_5647_ = (!lean_is_exclusive(v_a_5517_)) as u8;
                if v_isSharedCheck_5647_ == 0 {
                    v___x_5559_ = v_a_5517_;
                    v_isShared_5560_ = v_isSharedCheck_5647_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_5557_);
                    lean_inc(v_fst_5556_);
                    lean_dec(v_a_5517_);
                    v___x_5559_ = lean_box(0);
                    v_isShared_5560_ = v_isSharedCheck_5647_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_5524_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once
                    ),
                    _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4,
                );
                v___x_5525_ = l_Lean_MessageData_ofName(v_tacticName_5501_);
                v___x_5526_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5526_, 0, v___x_5524_);
                lean_ctor_set(v___x_5526_, 1, v___x_5525_);
                v___x_5527_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__2);
                v___x_5528_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5528_, 0, v___x_5526_);
                lean_ctor_set(v___x_5528_, 1, v___x_5527_);
                v___x_5529_ = l_Lean_indentExpr(v_expectedType_5502_);
                v___x_5530_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5530_, 0, v___x_5528_);
                lean_ctor_set(v___x_5530_, 1, v___x_5529_);
                v___x_5531_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__4);
                v___x_5532_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5532_, 0, v___x_5530_);
                lean_ctor_set(v___x_5532_, 1, v___x_5531_);
                v___x_5533_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2;
                v___x_5534_ = l_Lean_MessageData_ofConstName(v___x_5533_, v___x_5511_);
                v___x_5535_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5535_, 0, v___x_5532_);
                lean_ctor_set(v___x_5535_, 1, v___x_5534_);
                v___x_5536_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
                v___x_5537_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5537_, 0, v___x_5535_);
                lean_ctor_set(v___x_5537_, 1, v___x_5536_);
                v___x_5538_ = l_Lean_indentExpr(v_s_5503_);
                v___x_5539_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5539_, 0, v___x_5537_);
                lean_ctor_set(v___x_5539_, 1, v___x_5538_);
                v___x_5540_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__8);
                v___x_5541_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5541_, 0, v___x_5539_);
                lean_ctor_set(v___x_5541_, 1, v___x_5540_);
                v___x_5542_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5;
                v___x_5543_ = l_Lean_MessageData_ofConstName(v___x_5542_, v___x_5511_);
                v___x_5544_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5544_, 0, v___x_5541_);
                lean_ctor_set(v___x_5544_, 1, v___x_5543_);
                v___x_5545_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10);
                v___x_5546_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5546_, 0, v___x_5544_);
                lean_ctor_set(v___x_5546_, 1, v___x_5545_);
                v___x_5547_ = l_Lean_MessageData_ofConstName(v___x_5510_, v___x_5511_);
                v___x_5548_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5548_, 0, v___x_5546_);
                lean_ctor_set(v___x_5548_, 1, v___x_5547_);
                v___x_5549_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__12);
                v___x_5550_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5550_, 0, v___x_5548_);
                lean_ctor_set(v___x_5550_, 1, v___x_5549_);
                v___x_5551_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5551_, 0, v___x_5550_);
                lean_ctor_set(v___x_5551_, 1, v___y_5522_);
                v___x_5552_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5552_, 0, v___x_5551_);
                lean_ctor_set(v___x_5552_, 1, v___y_5523_);
                if v_isShared_5520_ == 0 {
                    lean_ctor_set(v___x_5519_, 0, v___x_5552_);
                    v___x_5554_ = v___x_5519_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5555_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5552_);
                    v___x_5554_ = v_reuseFailAlloc_5555_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5554_;
            }
            4 => {
                v___x_5632_ = lean_array_get_size(v_snd_5557_);
                v___x_5633_ = lean_unsigned_to_nat(0);
                v___x_5634_ = lean_nat_dec_eq(v___x_5632_, v___x_5633_);
                if v___x_5634_ == 0 {
                    v___x_5635_ = lean_unsigned_to_nat(1);
                    v___x_5636_ = lean_nat_dec_eq(v___x_5632_, v___x_5635_);
                    if v___x_5636_ == 0 {
                        v___x_5637_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__46;
                        v___y_5614_ = v___x_5637_;
                        state = 8;
                        continue;
                    } else {
                        v___x_5638_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__47;
                        v___y_5614_ = v___x_5638_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_5557_);
                    v___x_5639_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__49);
                    v___x_5640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2;
                    v___x_5641_ = l_Lean_MessageData_ofConstName(v___x_5640_, v___x_5511_);
                    v___x_5642_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5642_, 0, v___x_5639_);
                    lean_ctor_set(v___x_5642_, 1, v___x_5641_);
                    v___x_5643_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
                    v___x_5644_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5644_, 0, v___x_5642_);
                    lean_ctor_set(v___x_5644_, 1, v___x_5643_);
                    lean_inc(v_fst_5556_);
                    v___x_5645_ = l_Lean_indentExpr(v_fst_5556_);
                    v___x_5646_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5646_, 0, v___x_5644_);
                    lean_ctor_set(v___x_5646_, 1, v___x_5645_);
                    v___y_5562_ = v___x_5646_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5563_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__14;
                v___x_5564_ = l_Lean_Expr_isAppOf(v_fst_5556_, v___x_5563_);
                if v___x_5564_ == 0 {
                    v___x_5565_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__17;
                    v___x_5566_ = l_Lean_Expr_isAppOf(v_fst_5556_, v___x_5565_);
                    lean_dec(v_fst_5556_);
                    if v___x_5566_ == 0 {
                        lean_del_object(v___x_5559_);
                        v___x_5567_ = l_Lean_MessageData_nil;
                        v___y_5522_ = v___y_5562_;
                        v___y_5523_ = v___x_5567_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5568_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__19);
                        v___x_5569_ = l_Lean_MessageData_ofConstName(v___x_5565_, v___x_5511_);
                        if v_isShared_5560_ == 0 {
                            lean_ctor_set_tag(v___x_5559_, 7);
                            lean_ctor_set(v___x_5559_, 1, v___x_5569_);
                            lean_ctor_set(v___x_5559_, 0, v___x_5568_);
                            v___x_5571_ = v___x_5559_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5589_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5568_);
                            lean_ctor_set(v_reuseFailAlloc_5589_, 1, v___x_5569_);
                            v___x_5571_ = v_reuseFailAlloc_5589_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_5556_);
                    v___x_5590_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__29);
                    v___x_5591_ = l_Lean_MessageData_ofConstName(v___x_5563_, v___x_5511_);
                    if v_isShared_5560_ == 0 {
                        lean_ctor_set_tag(v___x_5559_, 7);
                        lean_ctor_set(v___x_5559_, 1, v___x_5591_);
                        lean_ctor_set(v___x_5559_, 0, v___x_5590_);
                        v___x_5593_ = v___x_5559_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5612_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5612_, 0, v___x_5590_);
                        lean_ctor_set(v_reuseFailAlloc_5612_, 1, v___x_5591_);
                        v___x_5593_ = v_reuseFailAlloc_5612_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v___x_5572_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__21);
                v___x_5573_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5573_, 0, v___x_5571_);
                lean_ctor_set(v___x_5573_, 1, v___x_5572_);
                v___x_5574_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2;
                v___x_5575_ = l_Lean_MessageData_ofConstName(v___x_5574_, v___x_5511_);
                v___x_5576_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5576_, 0, v___x_5573_);
                lean_ctor_set(v___x_5576_, 1, v___x_5575_);
                v___x_5577_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__23);
                v___x_5578_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5578_, 0, v___x_5576_);
                lean_ctor_set(v___x_5578_, 1, v___x_5577_);
                lean_inc(v_tacticName_5501_);
                v___x_5579_ = l_Lean_MessageData_ofName(v_tacticName_5501_);
                v___x_5580_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5580_, 0, v___x_5578_);
                lean_ctor_set(v___x_5580_, 1, v___x_5579_);
                v___x_5581_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__25);
                v___x_5582_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5582_, 0, v___x_5580_);
                lean_ctor_set(v___x_5582_, 1, v___x_5581_);
                v___x_5583_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__27;
                v___x_5584_ = l_Lean_MessageData_ofConstName(v___x_5583_, v___x_5511_);
                v___x_5585_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5585_, 0, v___x_5582_);
                lean_ctor_set(v___x_5585_, 1, v___x_5584_);
                v___x_5586_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg___closed__15);
                v___x_5587_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5587_, 0, v___x_5585_);
                lean_ctor_set(v___x_5587_, 1, v___x_5586_);
                v___x_5588_ = l_Lean_MessageData_hint_x27(v___x_5587_);
                v___y_5522_ = v___y_5562_;
                v___y_5523_ = v___x_5588_;
                state = 2;
                continue;
            }
            7 => {
                v___x_5594_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__31);
                v___x_5595_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5595_, 0, v___x_5593_);
                lean_ctor_set(v___x_5595_, 1, v___x_5594_);
                v___x_5596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2;
                v___x_5597_ = l_Lean_MessageData_ofConstName(v___x_5596_, v___x_5511_);
                v___x_5598_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5598_, 0, v___x_5595_);
                lean_ctor_set(v___x_5598_, 1, v___x_5597_);
                v___x_5599_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__33);
                v___x_5600_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5600_, 0, v___x_5598_);
                lean_ctor_set(v___x_5600_, 1, v___x_5599_);
                v___x_5601_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__35;
                v___x_5602_ = l_Lean_MessageData_ofConstName(v___x_5601_, v___x_5511_);
                v___x_5603_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5603_, 0, v___x_5600_);
                lean_ctor_set(v___x_5603_, 1, v___x_5602_);
                v___x_5604_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__10);
                v___x_5605_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5605_, 0, v___x_5603_);
                lean_ctor_set(v___x_5605_, 1, v___x_5604_);
                v___x_5606_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__37;
                v___x_5607_ = l_Lean_MessageData_ofConstName(v___x_5606_, v___x_5511_);
                v___x_5608_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5608_, 0, v___x_5605_);
                lean_ctor_set(v___x_5608_, 1, v___x_5607_);
                v___x_5609_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__39);
                v___x_5610_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5610_, 0, v___x_5608_);
                lean_ctor_set(v___x_5610_, 1, v___x_5609_);
                v___x_5611_ = l_Lean_MessageData_hint_x27(v___x_5610_);
                v___y_5522_ = v___y_5562_;
                v___y_5523_ = v___x_5611_;
                state = 2;
                continue;
            }
            8 => {
                v___x_5615_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__41);
                lean_inc_ref(v___y_5614_);
                v___x_5616_ = l_Lean_stringToMessageData(v___y_5614_);
                v___x_5617_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5617_, 0, v___x_5615_);
                lean_ctor_set(v___x_5617_, 1, v___x_5616_);
                v___x_5618_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__43);
                v___x_5619_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5619_, 0, v___x_5617_);
                lean_ctor_set(v___x_5619_, 1, v___x_5618_);
                v___x_5620_ = lean_array_to_list(v_snd_5557_);
                v___x_5621_ = l_Lean_MessageData_andList(v___x_5620_);
                v___x_5622_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5622_, 0, v___x_5619_);
                lean_ctor_set(v___x_5622_, 1, v___x_5621_);
                v___x_5623_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__45);
                v___x_5624_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5624_, 0, v___x_5622_);
                lean_ctor_set(v___x_5624_, 1, v___x_5623_);
                v___x_5625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2;
                v___x_5626_ = l_Lean_MessageData_ofConstName(v___x_5625_, v___x_5511_);
                v___x_5627_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5627_, 0, v___x_5624_);
                lean_ctor_set(v___x_5627_, 1, v___x_5626_);
                v___x_5628_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___closed__6);
                v___x_5629_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5629_, 0, v___x_5627_);
                lean_ctor_set(v___x_5629_, 1, v___x_5628_);
                lean_inc(v_fst_5556_);
                v___x_5630_ = l_Lean_indentExpr(v_fst_5556_);
                v___x_5631_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5631_, 0, v___x_5629_);
                lean_ctor_set(v___x_5631_, 1, v___x_5630_);
                v___y_5562_ = v___x_5631_;
                state = 5;
                continue;
            }
            9 => {
                if v_isShared_5652_ == 0 {
                    v___x_5654_ = v___x_5651_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5655_, 0, v_a_5649_);
                    v___x_5654_ = v_reuseFailAlloc_5655_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed(
    mut v_tacticName_5667_: *mut LeanObject,
    mut v_expectedType_5668_: *mut LeanObject,
    mut v_s_5669_: *mut LeanObject,
    mut v_r_5670_: *mut LeanObject,
    mut v_a_5671_: *mut LeanObject,
    mut v_a_5672_: *mut LeanObject,
    mut v_a_5673_: *mut LeanObject,
    mut v_a_5674_: *mut LeanObject,
    mut v_a_5675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5676_: *mut LeanObject = core::ptr::null_mut();
    v_res_5676_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(
        v_tacticName_5667_,
        v_expectedType_5668_,
        v_s_5669_,
        v_r_5670_,
        v_a_5671_,
        v_a_5672_,
        v_a_5673_,
        v_a_5674_,
    );
    lean_dec(v_a_5674_);
    lean_dec_ref(v_a_5673_);
    lean_dec(v_a_5672_);
    lean_dec_ref(v_a_5671_);
    lean_dec_ref(v_r_5670_);
    return v_res_5676_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(
    mut v_00_u03c3_5677_: *mut LeanObject,
    mut v_00_u03b2_5678_: *mut LeanObject,
    mut v_map_5679_: *mut LeanObject,
    mut v_f_5680_: *mut LeanObject,
    mut v_init_5681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5682_: *mut LeanObject = core::ptr::null_mut();
    v___x_5682_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___redArg(v_map_5679_, v_f_5680_, v_init_5681_);
    return v___x_5682_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3___boxed(
    mut v_00_u03c3_5683_: *mut LeanObject,
    mut v_00_u03b2_5684_: *mut LeanObject,
    mut v_map_5685_: *mut LeanObject,
    mut v_f_5686_: *mut LeanObject,
    mut v_init_5687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5688_: *mut LeanObject = core::ptr::null_mut();
    v_res_5688_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3(v_00_u03c3_5683_, v_00_u03b2_5684_, v_map_5685_, v_f_5686_, v_init_5687_);
    lean_dec_ref(v_map_5685_);
    return v_res_5688_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(
    mut v_n_5689_: *mut LeanObject,
    mut v_as_5690_: *mut LeanObject,
    mut v_lo_5691_: *mut LeanObject,
    mut v_hi_5692_: *mut LeanObject,
    mut v_w_5693_: *mut LeanObject,
    mut v_hlo_5694_: *mut LeanObject,
    mut v_hhi_5695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    v___x_5696_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___redArg(v_n_5689_, v_as_5690_, v_lo_5691_, v_hi_5692_);
    return v___x_5696_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5___boxed(
    mut v_n_5697_: *mut LeanObject,
    mut v_as_5698_: *mut LeanObject,
    mut v_lo_5699_: *mut LeanObject,
    mut v_hi_5700_: *mut LeanObject,
    mut v_w_5701_: *mut LeanObject,
    mut v_hlo_5702_: *mut LeanObject,
    mut v_hhi_5703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5704_: *mut LeanObject = core::ptr::null_mut();
    v_res_5704_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5(v_n_5697_, v_as_5698_, v_lo_5699_, v_hi_5700_, v_w_5701_, v_hlo_5702_, v_hhi_5703_);
    lean_dec(v_hi_5700_);
    lean_dec(v_n_5697_);
    return v_res_5704_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg(
    mut v_map_5705_: *mut LeanObject,
    mut v_f_5706_: *mut LeanObject,
    mut v_init_5707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5708_: *mut LeanObject = core::ptr::null_mut();
    v___x_5708_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_5706_, v_map_5705_, v_init_5707_);
    return v___x_5708_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg___boxed(
    mut v_map_5709_: *mut LeanObject,
    mut v_f_5710_: *mut LeanObject,
    mut v_init_5711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5712_: *mut LeanObject = core::ptr::null_mut();
    v_res_5712_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___redArg(v_map_5709_, v_f_5710_, v_init_5711_);
    lean_dec_ref(v_map_5709_);
    return v_res_5712_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6(
    mut v_00_u03c3_5713_: *mut LeanObject,
    mut v_00_u03b2_5714_: *mut LeanObject,
    mut v_map_5715_: *mut LeanObject,
    mut v_f_5716_: *mut LeanObject,
    mut v_init_5717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    v___x_5718_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_5716_, v_map_5715_, v_init_5717_);
    return v___x_5718_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6___boxed(
    mut v_00_u03c3_5719_: *mut LeanObject,
    mut v_00_u03b2_5720_: *mut LeanObject,
    mut v_map_5721_: *mut LeanObject,
    mut v_f_5722_: *mut LeanObject,
    mut v_init_5723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5724_: *mut LeanObject = core::ptr::null_mut();
    v_res_5724_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6(v_00_u03c3_5719_, v_00_u03b2_5720_, v_map_5721_, v_f_5722_, v_init_5723_);
    lean_dec_ref(v_map_5721_);
    return v_res_5724_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10(
    mut v_n_5725_: *mut LeanObject,
    mut v_lo_5726_: *mut LeanObject,
    mut v_hi_5727_: *mut LeanObject,
    mut v_hhi_5728_: *mut LeanObject,
    mut v_pivot_5729_: *mut LeanObject,
    mut v_as_5730_: *mut LeanObject,
    mut v_i_5731_: *mut LeanObject,
    mut v_k_5732_: *mut LeanObject,
    mut v_ilo_5733_: *mut LeanObject,
    mut v_ik_5734_: *mut LeanObject,
    mut v_w_5735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    v___x_5736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___redArg(v_hi_5727_, v_pivot_5729_, v_as_5730_, v_i_5731_, v_k_5732_);
    return v___x_5736_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10___boxed(
    mut v_n_5737_: *mut LeanObject,
    mut v_lo_5738_: *mut LeanObject,
    mut v_hi_5739_: *mut LeanObject,
    mut v_hhi_5740_: *mut LeanObject,
    mut v_pivot_5741_: *mut LeanObject,
    mut v_as_5742_: *mut LeanObject,
    mut v_i_5743_: *mut LeanObject,
    mut v_k_5744_: *mut LeanObject,
    mut v_ilo_5745_: *mut LeanObject,
    mut v_ik_5746_: *mut LeanObject,
    mut v_w_5747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5748_: *mut LeanObject = core::ptr::null_mut();
    v_res_5748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__5_spec__10(v_n_5737_, v_lo_5738_, v_hi_5739_, v_hhi_5740_, v_pivot_5741_, v_as_5742_, v_i_5743_, v_k_5744_, v_ilo_5745_, v_ik_5746_, v_w_5747_);
    lean_dec(v_pivot_5741_);
    lean_dec(v_hi_5739_);
    lean_dec(v_lo_5738_);
    lean_dec(v_n_5737_);
    return v_res_5748_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5(
    mut v_00_u03b1_5749_: *mut LeanObject,
    mut v_constName_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    v___x_5756_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___redArg(v_constName_5750_, v___y_5751_, v___y_5752_, v___y_5753_, v___y_5754_);
    return v___x_5756_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_5757_: *mut LeanObject,
    mut v_constName_5758_: *mut LeanObject,
    mut v___y_5759_: *mut LeanObject,
    mut v___y_5760_: *mut LeanObject,
    mut v___y_5761_: *mut LeanObject,
    mut v___y_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5764_: *mut LeanObject = core::ptr::null_mut();
    v_res_5764_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5(v_00_u03b1_5757_, v_constName_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_);
    lean_dec(v___y_5762_);
    lean_dec_ref(v___y_5761_);
    lean_dec(v___y_5760_);
    lean_dec_ref(v___y_5759_);
    return v_res_5764_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9(
    mut v_00_u03c3_5765_: *mut LeanObject,
    mut v_00_u03b1_5766_: *mut LeanObject,
    mut v_00_u03b2_5767_: *mut LeanObject,
    mut v_f_5768_: *mut LeanObject,
    mut v_x_5769_: *mut LeanObject,
    mut v_x_5770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    v___x_5771_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___redArg(v_f_5768_, v_x_5769_, v_x_5770_);
    return v___x_5771_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9___boxed(
    mut v_00_u03c3_5772_: *mut LeanObject,
    mut v_00_u03b1_5773_: *mut LeanObject,
    mut v_00_u03b2_5774_: *mut LeanObject,
    mut v_f_5775_: *mut LeanObject,
    mut v_x_5776_: *mut LeanObject,
    mut v_x_5777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5778_: *mut LeanObject = core::ptr::null_mut();
    v_res_5778_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9(v_00_u03c3_5772_, v_00_u03b1_5773_, v_00_u03b2_5774_, v_f_5775_, v_x_5776_, v_x_5777_);
    lean_dec_ref(v_x_5776_);
    return v_res_5778_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9(
    mut v_00_u03b1_5779_: *mut LeanObject,
    mut v_ref_5780_: *mut LeanObject,
    mut v_constName_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5787_: *mut LeanObject = core::ptr::null_mut();
    v___x_5787_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg(v_ref_5780_, v_constName_5781_, v___y_5782_, v___y_5783_, v___y_5784_, v___y_5785_);
    return v___x_5787_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___boxed(
    mut v_00_u03b1_5788_: *mut LeanObject,
    mut v_ref_5789_: *mut LeanObject,
    mut v_constName_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5796_: *mut LeanObject = core::ptr::null_mut();
    v_res_5796_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9(v_00_u03b1_5788_, v_ref_5789_, v_constName_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_);
    lean_dec(v___y_5794_);
    lean_dec_ref(v___y_5793_);
    lean_dec(v___y_5792_);
    lean_dec_ref(v___y_5791_);
    lean_dec(v_ref_5789_);
    return v_res_5796_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13(
    mut v_00_u03b1_5797_: *mut LeanObject,
    mut v_00_u03b2_5798_: *mut LeanObject,
    mut v_00_u03c3_5799_: *mut LeanObject,
    mut v_f_5800_: *mut LeanObject,
    mut v_as_5801_: *mut LeanObject,
    mut v_i_5802_: usize,
    mut v_stop_5803_: usize,
    mut v_b_5804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    v___x_5805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___redArg(v_f_5800_, v_as_5801_, v_i_5802_, v_stop_5803_, v_b_5804_);
    return v___x_5805_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13___boxed(
    mut v_00_u03b1_5806_: *mut LeanObject,
    mut v_00_u03b2_5807_: *mut LeanObject,
    mut v_00_u03c3_5808_: *mut LeanObject,
    mut v_f_5809_: *mut LeanObject,
    mut v_as_5810_: *mut LeanObject,
    mut v_i_5811_: *mut LeanObject,
    mut v_stop_5812_: *mut LeanObject,
    mut v_b_5813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5814_: usize = 0;
    let mut v_stop_boxed_5815_: usize = 0;
    let mut v_res_5816_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5814_ = lean_unbox_usize(v_i_5811_);
    lean_dec(v_i_5811_);
    v_stop_boxed_5815_ = lean_unbox_usize(v_stop_5812_);
    lean_dec(v_stop_5812_);
    v_res_5816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__13(v_00_u03b1_5806_, v_00_u03b2_5807_, v_00_u03c3_5808_, v_f_5809_, v_as_5810_, v_i_boxed_5814_, v_stop_boxed_5815_, v_b_5813_);
    lean_dec_ref(v_as_5810_);
    return v_res_5816_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14(
    mut v_00_u03c3_5817_: *mut LeanObject,
    mut v_00_u03b1_5818_: *mut LeanObject,
    mut v_00_u03b2_5819_: *mut LeanObject,
    mut v_f_5820_: *mut LeanObject,
    mut v_keys_5821_: *mut LeanObject,
    mut v_vals_5822_: *mut LeanObject,
    mut v_heq_5823_: *mut LeanObject,
    mut v_i_5824_: *mut LeanObject,
    mut v_acc_5825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5826_: *mut LeanObject = core::ptr::null_mut();
    v___x_5826_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___redArg(v_f_5820_, v_keys_5821_, v_vals_5822_, v_i_5824_, v_acc_5825_);
    return v___x_5826_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14___boxed(
    mut v_00_u03c3_5827_: *mut LeanObject,
    mut v_00_u03b1_5828_: *mut LeanObject,
    mut v_00_u03b2_5829_: *mut LeanObject,
    mut v_f_5830_: *mut LeanObject,
    mut v_keys_5831_: *mut LeanObject,
    mut v_vals_5832_: *mut LeanObject,
    mut v_heq_5833_: *mut LeanObject,
    mut v_i_5834_: *mut LeanObject,
    mut v_acc_5835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5836_: *mut LeanObject = core::ptr::null_mut();
    v_res_5836_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__3_spec__6_spec__9_spec__14(v_00_u03c3_5827_, v_00_u03b1_5828_, v_00_u03b2_5829_, v_f_5830_, v_keys_5831_, v_vals_5832_, v_heq_5833_, v_i_5834_, v_acc_5835_);
    lean_dec_ref(v_vals_5832_);
    lean_dec_ref(v_keys_5831_);
    return v_res_5836_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14(
    mut v_00_u03b1_5837_: *mut LeanObject,
    mut v_ref_5838_: *mut LeanObject,
    mut v_msg_5839_: *mut LeanObject,
    mut v_declHint_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    v___x_5846_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___redArg(v_ref_5838_, v_msg_5839_, v_declHint_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
    return v___x_5846_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14___boxed(
    mut v_00_u03b1_5847_: *mut LeanObject,
    mut v_ref_5848_: *mut LeanObject,
    mut v_msg_5849_: *mut LeanObject,
    mut v_declHint_5850_: *mut LeanObject,
    mut v___y_5851_: *mut LeanObject,
    mut v___y_5852_: *mut LeanObject,
    mut v___y_5853_: *mut LeanObject,
    mut v___y_5854_: *mut LeanObject,
    mut v___y_5855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5856_: *mut LeanObject = core::ptr::null_mut();
    v_res_5856_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14(v_00_u03b1_5847_, v_ref_5848_, v_msg_5849_, v_declHint_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_);
    lean_dec(v___y_5854_);
    lean_dec_ref(v___y_5853_);
    lean_dec(v___y_5852_);
    lean_dec_ref(v___y_5851_);
    lean_dec(v_ref_5848_);
    return v_res_5856_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19(
    mut v_msg_5857_: *mut LeanObject,
    mut v_declHint_5858_: *mut LeanObject,
    mut v___y_5859_: *mut LeanObject,
    mut v___y_5860_: *mut LeanObject,
    mut v___y_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    v___x_5864_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___redArg(v_msg_5857_, v_declHint_5858_, v___y_5862_);
    return v___x_5864_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19___boxed(
    mut v_msg_5865_: *mut LeanObject,
    mut v_declHint_5866_: *mut LeanObject,
    mut v___y_5867_: *mut LeanObject,
    mut v___y_5868_: *mut LeanObject,
    mut v___y_5869_: *mut LeanObject,
    mut v___y_5870_: *mut LeanObject,
    mut v___y_5871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5872_: *mut LeanObject = core::ptr::null_mut();
    v_res_5872_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__16_spec__19(v_msg_5865_, v_declHint_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
    lean_dec(v___y_5870_);
    lean_dec_ref(v___y_5869_);
    lean_dec(v___y_5868_);
    lean_dec_ref(v___y_5867_);
    return v_res_5872_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17(
    mut v_00_u03b1_5873_: *mut LeanObject,
    mut v_ref_5874_: *mut LeanObject,
    mut v_msg_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
    mut v___y_5877_: *mut LeanObject,
    mut v___y_5878_: *mut LeanObject,
    mut v___y_5879_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    v___x_5881_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___redArg(v_ref_5874_, v_msg_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_);
    return v___x_5881_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17___boxed(
    mut v_00_u03b1_5882_: *mut LeanObject,
    mut v_ref_5883_: *mut LeanObject,
    mut v_msg_5884_: *mut LeanObject,
    mut v___y_5885_: *mut LeanObject,
    mut v___y_5886_: *mut LeanObject,
    mut v___y_5887_: *mut LeanObject,
    mut v___y_5888_: *mut LeanObject,
    mut v___y_5889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5890_: *mut LeanObject = core::ptr::null_mut();
    v_res_5890_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17(v_00_u03b1_5882_, v_ref_5883_, v_msg_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
    lean_dec(v___y_5888_);
    lean_dec_ref(v___y_5887_);
    lean_dec(v___y_5886_);
    lean_dec_ref(v___y_5885_);
    lean_dec(v_ref_5883_);
    return v_res_5890_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21(
    mut v_00_u03b1_5891_: *mut LeanObject,
    mut v_msg_5892_: *mut LeanObject,
    mut v___y_5893_: *mut LeanObject,
    mut v___y_5894_: *mut LeanObject,
    mut v___y_5895_: *mut LeanObject,
    mut v___y_5896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    v___x_5898_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(v_msg_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_);
    return v___x_5898_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___boxed(
    mut v_00_u03b1_5899_: *mut LeanObject,
    mut v_msg_5900_: *mut LeanObject,
    mut v___y_5901_: *mut LeanObject,
    mut v___y_5902_: *mut LeanObject,
    mut v___y_5903_: *mut LeanObject,
    mut v___y_5904_: *mut LeanObject,
    mut v___y_5905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5906_: *mut LeanObject = core::ptr::null_mut();
    v_res_5906_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21(v_00_u03b1_5899_, v_msg_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_);
    lean_dec(v___y_5904_);
    lean_dec_ref(v___y_5903_);
    lean_dec(v___y_5902_);
    lean_dec_ref(v___y_5901_);
    return v_res_5906_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(
    mut v_tacticName_5907_: *mut LeanObject,
    mut v_expectedType_5908_: *mut LeanObject,
    mut v_a_5909_: *mut LeanObject,
    mut v_a_5910_: *mut LeanObject,
    mut v_a_5911_: *mut LeanObject,
    mut v_a_5912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_5917_: u8 = 0;
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5921_: u8 = 0;
    let mut v_foApprox_5922_: u8 = 0;
    let mut v_ctxApprox_5923_: u8 = 0;
    let mut v_quasiPatternApprox_5924_: u8 = 0;
    let mut v_constApprox_5925_: u8 = 0;
    let mut v_isDefEqStuckEx_5926_: u8 = 0;
    let mut v_unificationHints_5927_: u8 = 0;
    let mut v_proofIrrelevance_5928_: u8 = 0;
    let mut v_assignSyntheticOpaque_5929_: u8 = 0;
    let mut v_offsetCnstrs_5930_: u8 = 0;
    let mut v_etaStruct_5931_: u8 = 0;
    let mut v_univApprox_5932_: u8 = 0;
    let mut v_iota_5933_: u8 = 0;
    let mut v_beta_5934_: u8 = 0;
    let mut v_proj_5935_: u8 = 0;
    let mut v_zeta_5936_: u8 = 0;
    let mut v_zetaDelta_5937_: u8 = 0;
    let mut v_zetaUnused_5938_: u8 = 0;
    let mut v_zetaHave_5939_: u8 = 0;
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5942_: u8 = 0;
    let mut v_trackZetaDelta_5943_: u8 = 0;
    let mut v_zetaDeltaSet_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5950_: u8 = 0;
    let mut v_inTypeClassResolution_5951_: u8 = 0;
    let mut v_cacheInferType_5952_: u8 = 0;
    let mut v_config_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u64 = 0;
    let mut v___x_5956_: u64 = 0;
    let mut v___x_5957_: u64 = 0;
    let mut v___x_5958_: u64 = 0;
    let mut v___x_5959_: u64 = 0;
    let mut v_key_5960_: u64 = 0;
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5967_: u8 = 0;
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: u8 = 0;
    let mut v___x_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5979_: u8 = 0;
    let mut v_reuseFailAlloc_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v___x_5982_: u8 = 0;
    let mut v___x_5983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_expectedType_5908_);
                v___x_5914_ = l_Lean_Meta_mkDecideProof(
                    v_expectedType_5908_,
                    v_a_5909_,
                    v_a_5910_,
                    v_a_5911_,
                    v_a_5912_,
                );
                if lean_obj_tag(v___x_5914_) == 0 {
                    v_a_5915_ = lean_ctor_get(v___x_5914_, 0);
                    lean_inc(v_a_5915_);
                    lean_dec_ref_known(v___x_5914_, 1);
                    v___x_5916_ = l_Lean_Meta_Context_config(v_a_5909_);
                    v_transparency_5917_ = lean_ctor_get_uint8(v___x_5916_, 9 as u32);
                    v___x_5918_ = l_Lean_Expr_appFn_x21(v_a_5915_);
                    v___x_5919_ = l_Lean_Expr_appArg_x21(v___x_5918_);
                    lean_dec_ref(v___x_5918_);
                    v___x_5982_ = 1;
                    v___x_5983_ =
                        l_Lean_Meta_TransparencyMode_lt(v_transparency_5917_, v___x_5982_);
                    if v___x_5983_ == 0 {
                        v___y_5921_ = v_transparency_5917_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5921_ = v___x_5982_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_expectedType_5908_);
                    lean_dec(v_tacticName_5907_);
                    return v___x_5914_;
                }
            }
            1 => {
                v_foApprox_5922_ = lean_ctor_get_uint8(v___x_5916_, 0 as u32);
                v_ctxApprox_5923_ = lean_ctor_get_uint8(v___x_5916_, 1 as u32);
                v_quasiPatternApprox_5924_ = lean_ctor_get_uint8(v___x_5916_, 2 as u32);
                v_constApprox_5925_ = lean_ctor_get_uint8(v___x_5916_, 3 as u32);
                v_isDefEqStuckEx_5926_ = lean_ctor_get_uint8(v___x_5916_, 4 as u32);
                v_unificationHints_5927_ = lean_ctor_get_uint8(v___x_5916_, 5 as u32);
                v_proofIrrelevance_5928_ = lean_ctor_get_uint8(v___x_5916_, 6 as u32);
                v_assignSyntheticOpaque_5929_ = lean_ctor_get_uint8(v___x_5916_, 7 as u32);
                v_offsetCnstrs_5930_ = lean_ctor_get_uint8(v___x_5916_, 8 as u32);
                v_etaStruct_5931_ = lean_ctor_get_uint8(v___x_5916_, 10 as u32);
                v_univApprox_5932_ = lean_ctor_get_uint8(v___x_5916_, 11 as u32);
                v_iota_5933_ = lean_ctor_get_uint8(v___x_5916_, 12 as u32);
                v_beta_5934_ = lean_ctor_get_uint8(v___x_5916_, 13 as u32);
                v_proj_5935_ = lean_ctor_get_uint8(v___x_5916_, 14 as u32);
                v_zeta_5936_ = lean_ctor_get_uint8(v___x_5916_, 15 as u32);
                v_zetaDelta_5937_ = lean_ctor_get_uint8(v___x_5916_, 16 as u32);
                v_zetaUnused_5938_ = lean_ctor_get_uint8(v___x_5916_, 17 as u32);
                v_zetaHave_5939_ = lean_ctor_get_uint8(v___x_5916_, 18 as u32);
                v_isSharedCheck_5981_ = (!lean_is_exclusive(v___x_5916_)) as u8;
                if v_isSharedCheck_5981_ == 0 {
                    v___x_5941_ = v___x_5916_;
                    v_isShared_5942_ = v_isSharedCheck_5981_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_5916_);
                    v___x_5941_ = lean_box(0);
                    v_isShared_5942_ = v_isSharedCheck_5981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_5943_ = lean_ctor_get_uint8(
                    v_a_5909_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5944_ = lean_ctor_get(v_a_5909_, 1);
                v_lctx_5945_ = lean_ctor_get(v_a_5909_, 2);
                v_localInstances_5946_ = lean_ctor_get(v_a_5909_, 3);
                v_defEqCtx_x3f_5947_ = lean_ctor_get(v_a_5909_, 4);
                v_synthPendingDepth_5948_ = lean_ctor_get(v_a_5909_, 5);
                v_canUnfold_x3f_5949_ = lean_ctor_get(v_a_5909_, 6);
                v_univApprox_5950_ = lean_ctor_get_uint8(
                    v_a_5909_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5951_ = lean_ctor_get_uint8(
                    v_a_5909_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5952_ = lean_ctor_get_uint8(
                    v_a_5909_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_5942_ == 0 {
                    v_config_5954_ = v___x_5941_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5980_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 0 as u32, v_foApprox_5922_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 1 as u32, v_ctxApprox_5923_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5980_,
                        2 as u32,
                        v_quasiPatternApprox_5924_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 3 as u32, v_constApprox_5925_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 4 as u32, v_isDefEqStuckEx_5926_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 5 as u32, v_unificationHints_5927_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 6 as u32, v_proofIrrelevance_5928_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5980_,
                        7 as u32,
                        v_assignSyntheticOpaque_5929_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 8 as u32, v_offsetCnstrs_5930_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 10 as u32, v_etaStruct_5931_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 11 as u32, v_univApprox_5932_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 12 as u32, v_iota_5933_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 13 as u32, v_beta_5934_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 14 as u32, v_proj_5935_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 15 as u32, v_zeta_5936_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 16 as u32, v_zetaDelta_5937_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 17 as u32, v_zetaUnused_5938_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_5980_, 18 as u32, v_zetaHave_5939_);
                    v_config_5954_ = v_reuseFailAlloc_5980_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_5954_, 9 as u32, v___y_5921_);
                v___x_5955_ = l_Lean_Meta_Context_configKey(v_a_5909_);
                v___x_5956_ = 3u64;
                v___x_5957_ = lean_uint64_shift_right(v___x_5955_, v___x_5956_);
                v___x_5958_ = lean_uint64_shift_left(v___x_5957_, v___x_5956_);
                v___x_5959_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_5921_);
                v_key_5960_ = lean_uint64_lor(v___x_5958_, v___x_5959_);
                v___x_5961_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_5961_, 0, v_config_5954_);
                lean_ctor_set_uint64(
                    v___x_5961_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_5960_,
                );
                lean_inc(v_canUnfold_x3f_5949_);
                lean_inc(v_synthPendingDepth_5948_);
                lean_inc(v_defEqCtx_x3f_5947_);
                lean_inc_ref(v_localInstances_5946_);
                lean_inc_ref(v_lctx_5945_);
                lean_inc(v_zetaDeltaSet_5944_);
                v___x_5962_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_5962_, 0, v___x_5961_);
                lean_ctor_set(v___x_5962_, 1, v_zetaDeltaSet_5944_);
                lean_ctor_set(v___x_5962_, 2, v_lctx_5945_);
                lean_ctor_set(v___x_5962_, 3, v_localInstances_5946_);
                lean_ctor_set(v___x_5962_, 4, v_defEqCtx_x3f_5947_);
                lean_ctor_set(v___x_5962_, 5, v_synthPendingDepth_5948_);
                lean_ctor_set(v___x_5962_, 6, v_canUnfold_x3f_5949_);
                lean_ctor_set_uint8(
                    v___x_5962_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5943_,
                );
                lean_ctor_set_uint8(
                    v___x_5962_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5950_,
                );
                lean_ctor_set_uint8(
                    v___x_5962_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5951_,
                );
                lean_ctor_set_uint8(
                    v___x_5962_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5952_,
                );
                lean_inc(v_a_5912_);
                lean_inc_ref(v_a_5911_);
                lean_inc(v_a_5910_);
                lean_inc_ref(v___x_5919_);
                v___x_5963_ = lean_whnf(v___x_5919_, v___x_5962_, v_a_5910_, v_a_5911_, v_a_5912_);
                if lean_obj_tag(v___x_5963_) == 0 {
                    v_a_5964_ = lean_ctor_get(v___x_5963_, 0);
                    v_isSharedCheck_5979_ = (!lean_is_exclusive(v___x_5963_)) as u8;
                    if v_isSharedCheck_5979_ == 0 {
                        v___x_5966_ = v___x_5963_;
                        v_isShared_5967_ = v_isSharedCheck_5979_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5964_);
                        lean_dec(v___x_5963_);
                        v___x_5966_ = lean_box(0);
                        v_isShared_5967_ = v_isSharedCheck_5979_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_5919_);
                    lean_dec(v_a_5915_);
                    lean_dec_ref(v_expectedType_5908_);
                    lean_dec(v_tacticName_5907_);
                    return v___x_5963_;
                }
            }
            4 => {
                v___x_5968_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5;
                v___x_5969_ = l_Lean_Expr_isAppOf(v_a_5964_, v___x_5968_);
                if v___x_5969_ == 0 {
                    lean_del_object(v___x_5966_);
                    lean_dec(v_a_5915_);
                    lean_inc_ref(v_expectedType_5908_);
                    v___x_5970_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___boxed as *mut core::ffi::c_void, 9, 4);
                    lean_closure_set(v___x_5970_, 0, v_tacticName_5907_);
                    lean_closure_set(v___x_5970_, 1, v_expectedType_5908_);
                    lean_closure_set(v___x_5970_, 2, v___x_5919_);
                    lean_closure_set(v___x_5970_, 3, v_a_5964_);
                    v___x_5971_ = lean_unsigned_to_nat(1);
                    v___x_5972_ = lean_mk_empty_array_with_capacity(v___x_5971_);
                    v___x_5973_ = lean_array_push(v___x_5972_, v_expectedType_5908_);
                    v___x_5974_ = l_Lean_MessageData_ofLazyM(v___x_5970_, v___x_5973_);
                    v___x_5975_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_5974_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_);
                    return v___x_5975_;
                } else {
                    lean_dec(v_a_5964_);
                    lean_dec_ref(v___x_5919_);
                    lean_dec_ref(v_expectedType_5908_);
                    lean_dec(v_tacticName_5907_);
                    if v_isShared_5967_ == 0 {
                        lean_ctor_set(v___x_5966_, 0, v_a_5915_);
                        v___x_5977_ = v___x_5966_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5978_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5978_, 0, v_a_5915_);
                        v___x_5977_ = v_reuseFailAlloc_5978_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg___boxed(
    mut v_tacticName_5984_: *mut LeanObject,
    mut v_expectedType_5985_: *mut LeanObject,
    mut v_a_5986_: *mut LeanObject,
    mut v_a_5987_: *mut LeanObject,
    mut v_a_5988_: *mut LeanObject,
    mut v_a_5989_: *mut LeanObject,
    mut v_a_5990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5991_: *mut LeanObject = core::ptr::null_mut();
    v_res_5991_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(
            v_tacticName_5984_,
            v_expectedType_5985_,
            v_a_5986_,
            v_a_5987_,
            v_a_5988_,
            v_a_5989_,
        );
    lean_dec(v_a_5989_);
    lean_dec_ref(v_a_5988_);
    lean_dec(v_a_5987_);
    lean_dec_ref(v_a_5986_);
    return v_res_5991_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(
    mut v_tacticName_5992_: *mut LeanObject,
    mut v_expectedType_5993_: *mut LeanObject,
    mut v_a_5994_: *mut LeanObject,
    mut v_a_5995_: *mut LeanObject,
    mut v_a_5996_: *mut LeanObject,
    mut v_a_5997_: *mut LeanObject,
    mut v_a_5998_: *mut LeanObject,
    mut v_a_5999_: *mut LeanObject,
    mut v_a_6000_: *mut LeanObject,
    mut v_a_6001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    v___x_6003_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(
            v_tacticName_5992_,
            v_expectedType_5993_,
            v_a_5998_,
            v_a_5999_,
            v_a_6000_,
            v_a_6001_,
        );
    return v___x_6003_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___boxed(
    mut v_tacticName_6004_: *mut LeanObject,
    mut v_expectedType_6005_: *mut LeanObject,
    mut v_a_6006_: *mut LeanObject,
    mut v_a_6007_: *mut LeanObject,
    mut v_a_6008_: *mut LeanObject,
    mut v_a_6009_: *mut LeanObject,
    mut v_a_6010_: *mut LeanObject,
    mut v_a_6011_: *mut LeanObject,
    mut v_a_6012_: *mut LeanObject,
    mut v_a_6013_: *mut LeanObject,
    mut v_a_6014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6015_: *mut LeanObject = core::ptr::null_mut();
    v_res_6015_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab(
        v_tacticName_6004_,
        v_expectedType_6005_,
        v_a_6006_,
        v_a_6007_,
        v_a_6008_,
        v_a_6009_,
        v_a_6010_,
        v_a_6011_,
        v_a_6012_,
        v_a_6013_,
    );
    lean_dec(v_a_6013_);
    lean_dec_ref(v_a_6012_);
    lean_dec(v_a_6011_);
    lean_dec_ref(v_a_6010_);
    lean_dec(v_a_6009_);
    lean_dec_ref(v_a_6008_);
    lean_dec(v_a_6007_);
    lean_dec_ref(v_a_6006_);
    return v_res_6015_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    v___x_6017_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__0;
    v___x_6018_ = l_Lean_stringToMessageData(v___x_6017_);
    return v___x_6018_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    v___x_6020_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__2;
    v___x_6021_ = l_Lean_stringToMessageData(v___x_6020_);
    return v___x_6021_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(
    mut v___x_6022_: *mut LeanObject,
    mut v_tacticName_6023_: *mut LeanObject,
    mut v_expectedType_6024_: *mut LeanObject,
    mut v___x_6025_: u8,
    mut v_a_6026_: *mut LeanObject,
    mut v___x_6027_: u8,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6034_: u8 = 0;
    let mut v___x_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_6036_: u8 = 0;
    let mut v_ctxApprox_6037_: u8 = 0;
    let mut v_quasiPatternApprox_6038_: u8 = 0;
    let mut v_constApprox_6039_: u8 = 0;
    let mut v_isDefEqStuckEx_6040_: u8 = 0;
    let mut v_unificationHints_6041_: u8 = 0;
    let mut v_proofIrrelevance_6042_: u8 = 0;
    let mut v_assignSyntheticOpaque_6043_: u8 = 0;
    let mut v_offsetCnstrs_6044_: u8 = 0;
    let mut v_etaStruct_6045_: u8 = 0;
    let mut v_univApprox_6046_: u8 = 0;
    let mut v_iota_6047_: u8 = 0;
    let mut v_beta_6048_: u8 = 0;
    let mut v_proj_6049_: u8 = 0;
    let mut v_zeta_6050_: u8 = 0;
    let mut v_zetaDelta_6051_: u8 = 0;
    let mut v_zetaUnused_6052_: u8 = 0;
    let mut v_zetaHave_6053_: u8 = 0;
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6056_: u8 = 0;
    let mut v_trackZetaDelta_6057_: u8 = 0;
    let mut v_zetaDeltaSet_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_6063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_6064_: u8 = 0;
    let mut v_inTypeClassResolution_6065_: u8 = 0;
    let mut v_cacheInferType_6066_: u8 = 0;
    let mut v_config_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: u64 = 0;
    let mut v___x_6070_: u64 = 0;
    let mut v___x_6071_: u64 = 0;
    let mut v___x_6072_: u64 = 0;
    let mut v___x_6073_: u64 = 0;
    let mut v_key_6074_: u64 = 0;
    let mut v___x_6075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6081_: u8 = 0;
    let mut v___x_6082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: u8 = 0;
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6101_: u8 = 0;
    let mut v_a_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6105_: u8 = 0;
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut v_reuseFailAlloc_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6111_: u8 = 0;
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_transparency_6113_: u8 = 0;
    let mut v___x_6114_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6112_ = l_Lean_Meta_Context_config(v___y_6028_);
                v_transparency_6113_ = lean_ctor_get_uint8(v___x_6112_, 9 as u32);
                lean_dec_ref(v___x_6112_);
                v___x_6114_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_6113_, v___x_6027_);
                if v___x_6114_ == 0 {
                    v___y_6034_ = v_transparency_6113_;
                    state = 1;
                    continue;
                } else {
                    v___y_6034_ = v___x_6027_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6035_ = l_Lean_Meta_Context_config(v___y_6028_);
                v_foApprox_6036_ = lean_ctor_get_uint8(v___x_6035_, 0 as u32);
                v_ctxApprox_6037_ = lean_ctor_get_uint8(v___x_6035_, 1 as u32);
                v_quasiPatternApprox_6038_ = lean_ctor_get_uint8(v___x_6035_, 2 as u32);
                v_constApprox_6039_ = lean_ctor_get_uint8(v___x_6035_, 3 as u32);
                v_isDefEqStuckEx_6040_ = lean_ctor_get_uint8(v___x_6035_, 4 as u32);
                v_unificationHints_6041_ = lean_ctor_get_uint8(v___x_6035_, 5 as u32);
                v_proofIrrelevance_6042_ = lean_ctor_get_uint8(v___x_6035_, 6 as u32);
                v_assignSyntheticOpaque_6043_ = lean_ctor_get_uint8(v___x_6035_, 7 as u32);
                v_offsetCnstrs_6044_ = lean_ctor_get_uint8(v___x_6035_, 8 as u32);
                v_etaStruct_6045_ = lean_ctor_get_uint8(v___x_6035_, 10 as u32);
                v_univApprox_6046_ = lean_ctor_get_uint8(v___x_6035_, 11 as u32);
                v_iota_6047_ = lean_ctor_get_uint8(v___x_6035_, 12 as u32);
                v_beta_6048_ = lean_ctor_get_uint8(v___x_6035_, 13 as u32);
                v_proj_6049_ = lean_ctor_get_uint8(v___x_6035_, 14 as u32);
                v_zeta_6050_ = lean_ctor_get_uint8(v___x_6035_, 15 as u32);
                v_zetaDelta_6051_ = lean_ctor_get_uint8(v___x_6035_, 16 as u32);
                v_zetaUnused_6052_ = lean_ctor_get_uint8(v___x_6035_, 17 as u32);
                v_zetaHave_6053_ = lean_ctor_get_uint8(v___x_6035_, 18 as u32);
                v_isSharedCheck_6111_ = (!lean_is_exclusive(v___x_6035_)) as u8;
                if v_isSharedCheck_6111_ == 0 {
                    v___x_6055_ = v___x_6035_;
                    v_isShared_6056_ = v_isSharedCheck_6111_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v___x_6035_);
                    v___x_6055_ = lean_box(0);
                    v_isShared_6056_ = v_isSharedCheck_6111_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_trackZetaDelta_6057_ = lean_ctor_get_uint8(
                    v___y_6028_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_6058_ = lean_ctor_get(v___y_6028_, 1);
                v_lctx_6059_ = lean_ctor_get(v___y_6028_, 2);
                v_localInstances_6060_ = lean_ctor_get(v___y_6028_, 3);
                v_defEqCtx_x3f_6061_ = lean_ctor_get(v___y_6028_, 4);
                v_synthPendingDepth_6062_ = lean_ctor_get(v___y_6028_, 5);
                v_canUnfold_x3f_6063_ = lean_ctor_get(v___y_6028_, 6);
                v_univApprox_6064_ = lean_ctor_get_uint8(
                    v___y_6028_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_6065_ = lean_ctor_get_uint8(
                    v___y_6028_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_6066_ = lean_ctor_get_uint8(
                    v___y_6028_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_6056_ == 0 {
                    v_config_6068_ = v___x_6055_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6110_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 0 as u32, v_foApprox_6036_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 1 as u32, v_ctxApprox_6037_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6110_,
                        2 as u32,
                        v_quasiPatternApprox_6038_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 3 as u32, v_constApprox_6039_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 4 as u32, v_isDefEqStuckEx_6040_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 5 as u32, v_unificationHints_6041_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 6 as u32, v_proofIrrelevance_6042_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6110_,
                        7 as u32,
                        v_assignSyntheticOpaque_6043_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 8 as u32, v_offsetCnstrs_6044_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 10 as u32, v_etaStruct_6045_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 11 as u32, v_univApprox_6046_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 12 as u32, v_iota_6047_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 13 as u32, v_beta_6048_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 14 as u32, v_proj_6049_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 15 as u32, v_zeta_6050_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 16 as u32, v_zetaDelta_6051_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 17 as u32, v_zetaUnused_6052_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6110_, 18 as u32, v_zetaHave_6053_);
                    v_config_6068_ = v_reuseFailAlloc_6110_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_6068_, 9 as u32, v___y_6034_);
                v___x_6069_ = l_Lean_Meta_Context_configKey(v___y_6028_);
                v___x_6070_ = 3u64;
                v___x_6071_ = lean_uint64_shift_right(v___x_6069_, v___x_6070_);
                v___x_6072_ = lean_uint64_shift_left(v___x_6071_, v___x_6070_);
                v___x_6073_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_6034_);
                v_key_6074_ = lean_uint64_lor(v___x_6072_, v___x_6073_);
                v___x_6075_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_6075_, 0, v_config_6068_);
                lean_ctor_set_uint64(
                    v___x_6075_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_6074_,
                );
                lean_inc(v_canUnfold_x3f_6063_);
                lean_inc(v_synthPendingDepth_6062_);
                lean_inc(v_defEqCtx_x3f_6061_);
                lean_inc_ref(v_localInstances_6060_);
                lean_inc_ref(v_lctx_6059_);
                lean_inc(v_zetaDeltaSet_6058_);
                v___x_6076_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_6076_, 0, v___x_6075_);
                lean_ctor_set(v___x_6076_, 1, v_zetaDeltaSet_6058_);
                lean_ctor_set(v___x_6076_, 2, v_lctx_6059_);
                lean_ctor_set(v___x_6076_, 3, v_localInstances_6060_);
                lean_ctor_set(v___x_6076_, 4, v_defEqCtx_x3f_6061_);
                lean_ctor_set(v___x_6076_, 5, v_synthPendingDepth_6062_);
                lean_ctor_set(v___x_6076_, 6, v_canUnfold_x3f_6063_);
                lean_ctor_set_uint8(
                    v___x_6076_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_6057_,
                );
                lean_ctor_set_uint8(
                    v___x_6076_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_6064_,
                );
                lean_ctor_set_uint8(
                    v___x_6076_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_6065_,
                );
                lean_ctor_set_uint8(
                    v___x_6076_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_6066_,
                );
                lean_inc(v___y_6031_);
                lean_inc_ref(v___y_6030_);
                lean_inc(v___y_6029_);
                lean_inc_ref(v___x_6022_);
                v___x_6077_ = lean_whnf(
                    v___x_6022_,
                    v___x_6076_,
                    v___y_6029_,
                    v___y_6030_,
                    v___y_6031_,
                );
                if lean_obj_tag(v___x_6077_) == 0 {
                    v_a_6078_ = lean_ctor_get(v___x_6077_, 0);
                    v_isSharedCheck_6101_ = (!lean_is_exclusive(v___x_6077_)) as u8;
                    if v_isSharedCheck_6101_ == 0 {
                        v___x_6080_ = v___x_6077_;
                        v_isShared_6081_ = v_isSharedCheck_6101_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6078_);
                        lean_dec(v___x_6077_);
                        v___x_6080_ = lean_box(0);
                        v_isShared_6081_ = v_isSharedCheck_6101_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___y_6031_);
                    lean_dec_ref(v___y_6030_);
                    lean_dec(v___y_6029_);
                    lean_dec_ref(v_a_6026_);
                    lean_dec_ref(v_expectedType_6024_);
                    lean_dec(v_tacticName_6023_);
                    lean_dec_ref(v___x_6022_);
                    v_a_6102_ = lean_ctor_get(v___x_6077_, 0);
                    v_isSharedCheck_6109_ = (!lean_is_exclusive(v___x_6077_)) as u8;
                    if v_isSharedCheck_6109_ == 0 {
                        v___x_6104_ = v___x_6077_;
                        v_isShared_6105_ = v_isSharedCheck_6109_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6102_);
                        lean_dec(v___x_6077_);
                        v___x_6104_ = lean_box(0);
                        v_isShared_6105_ = v_isSharedCheck_6109_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6082_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__5;
                v___x_6083_ = l_Lean_Expr_isAppOf(v_a_6078_, v___x_6082_);
                if v___x_6083_ == 0 {
                    lean_del_object(v___x_6080_);
                    lean_dec_ref(v_a_6026_);
                    v___x_6084_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose(v_tacticName_6023_, v_expectedType_6024_, v___x_6022_, v_a_6078_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_);
                    lean_dec(v___y_6031_);
                    lean_dec_ref(v___y_6030_);
                    lean_dec(v___y_6029_);
                    lean_dec(v_a_6078_);
                    return v___x_6084_;
                } else {
                    lean_dec(v_a_6078_);
                    lean_dec(v___y_6031_);
                    lean_dec_ref(v___y_6030_);
                    lean_dec(v___y_6029_);
                    lean_dec_ref(v_expectedType_6024_);
                    lean_dec_ref(v___x_6022_);
                    v___x_6085_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once
                        ),
                        _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4,
                    );
                    v___x_6086_ = l_Lean_MessageData_ofName(v_tacticName_6023_);
                    v___x_6087_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6087_, 0, v___x_6085_);
                    lean_ctor_set(v___x_6087_, 1, v___x_6086_);
                    v___x_6088_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__1);
                    v___x_6089_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6089_, 0, v___x_6087_);
                    lean_ctor_set(v___x_6089_, 1, v___x_6088_);
                    v___x_6090_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_blameDecideReductionFailure_spec__2___redArg___closed__2;
                    v___x_6091_ = l_Lean_MessageData_ofConstName(v___x_6090_, v___x_6025_);
                    v___x_6092_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6092_, 0, v___x_6089_);
                    lean_ctor_set(v___x_6092_, 1, v___x_6091_);
                    v___x_6093_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___closed__3);
                    v___x_6094_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6094_, 0, v___x_6092_);
                    lean_ctor_set(v___x_6094_, 1, v___x_6093_);
                    v___x_6095_ = l_Lean_Exception_toMessageData(v_a_6026_);
                    v___x_6096_ = l_Lean_indentD(v___x_6095_);
                    v___x_6097_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6097_, 0, v___x_6094_);
                    lean_ctor_set(v___x_6097_, 1, v___x_6096_);
                    if v_isShared_6081_ == 0 {
                        lean_ctor_set(v___x_6080_, 0, v___x_6097_);
                        v___x_6099_ = v___x_6080_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6100_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6100_, 0, v___x_6097_);
                        v___x_6099_ = v_reuseFailAlloc_6100_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_6099_;
            }
            6 => {
                if v_isShared_6105_ == 0 {
                    v___x_6107_ = v___x_6104_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6108_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6108_, 0, v_a_6102_);
                    v___x_6107_ = v_reuseFailAlloc_6108_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed(
    mut v___x_6115_: *mut LeanObject,
    mut v_tacticName_6116_: *mut LeanObject,
    mut v_expectedType_6117_: *mut LeanObject,
    mut v___x_6118_: *mut LeanObject,
    mut v_a_6119_: *mut LeanObject,
    mut v___x_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
    mut v___y_6122_: *mut LeanObject,
    mut v___y_6123_: *mut LeanObject,
    mut v___y_6124_: *mut LeanObject,
    mut v___y_6125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5937__boxed_6126_: u8 = 0;
    let mut v___x_5939__boxed_6127_: u8 = 0;
    let mut v_res_6128_: *mut LeanObject = core::ptr::null_mut();
    v___x_5937__boxed_6126_ = (lean_unbox(v___x_6118_) as u8);
    v___x_5939__boxed_6127_ = (lean_unbox(v___x_6120_) as u8);
    v_res_6128_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0(v___x_6115_, v_tacticName_6116_, v_expectedType_6117_, v___x_5937__boxed_6126_, v_a_6119_, v___x_5939__boxed_6127_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_);
    lean_dec_ref(v___y_6121_);
    return v_res_6128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(
    mut v_a_6129_: *mut LeanObject,
    mut v_as_6130_: *mut LeanObject,
    mut v_i_6131_: usize,
    mut v_stop_6132_: usize,
) -> u8 {
    let mut v___x_6133_: u8 = 0;
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: u8 = 0;
    let mut v___x_6136_: usize = 0;
    let mut v___x_6137_: usize = 0;
    let mut v___x_6139_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6133_ = lean_usize_dec_eq(v_i_6131_, v_stop_6132_);
                if v___x_6133_ == 0 {
                    v___x_6134_ = lean_array_uget_borrowed(v_as_6130_, v_i_6131_);
                    v___x_6135_ = lean_name_eq(v_a_6129_, v___x_6134_);
                    if v___x_6135_ == 0 {
                        v___x_6136_ = 1usize;
                        v___x_6137_ = lean_usize_add(v_i_6131_, v___x_6136_);
                        v_i_6131_ = v___x_6137_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6135_;
                    }
                } else {
                    v___x_6139_ = 0;
                    return v___x_6139_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0___boxed(
    mut v_a_6140_: *mut LeanObject,
    mut v_as_6141_: *mut LeanObject,
    mut v_i_6142_: *mut LeanObject,
    mut v_stop_6143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_6144_: usize = 0;
    let mut v_stop_boxed_6145_: usize = 0;
    let mut v_res_6146_: u8 = 0;
    let mut v_r_6147_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6144_ = lean_unbox_usize(v_i_6142_);
    lean_dec(v_i_6142_);
    v_stop_boxed_6145_ = lean_unbox_usize(v_stop_6143_);
    lean_dec(v_stop_6143_);
    v_res_6146_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_6140_, v_as_6141_, v_i_boxed_6144_, v_stop_boxed_6145_);
    lean_dec_ref(v_as_6141_);
    lean_dec(v_a_6140_);
    v_r_6147_ = lean_box((v_res_6146_) as usize);
    return v_r_6147_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(
    mut v_as_6148_: *mut LeanObject,
    mut v_a_6149_: *mut LeanObject,
) -> u8 {
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: u8 = 0;
    v___x_6150_ = lean_unsigned_to_nat(0);
    v___x_6151_ = lean_array_get_size(v_as_6148_);
    v___x_6152_ = lean_nat_dec_lt(v___x_6150_, v___x_6151_);
    if v___x_6152_ == 0 {
        return v___x_6152_;
    } else {
        if v___x_6152_ == 0 {
            return v___x_6152_;
        } else {
            let mut v___x_6153_: usize = 0;
            let mut v___x_6154_: usize = 0;
            let mut v___x_6155_: u8 = 0;
            v___x_6153_ = 0usize;
            v___x_6154_ = lean_usize_of_nat(v___x_6151_);
            v___x_6155_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0_spec__0(v_a_6149_, v_as_6148_, v___x_6153_, v___x_6154_);
            return v___x_6155_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0___boxed(
    mut v_as_6156_: *mut LeanObject,
    mut v_a_6157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6158_: u8 = 0;
    let mut v_r_6159_: *mut LeanObject = core::ptr::null_mut();
    v_res_6158_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v_as_6156_, v_a_6157_);
    lean_dec(v_a_6157_);
    lean_dec_ref(v_as_6156_);
    v_r_6159_ = lean_box((v_res_6158_) as usize);
    return v_r_6159_;
}
pub unsafe fn l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(
    mut v___x_6160_: *mut LeanObject,
    mut v_a_6161_: *mut LeanObject,
    mut v_a_6162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6168_: u8 = 0;
    let mut v___x_6169_: u8 = 0;
    let mut v___x_6172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6161_) == 0 {
                    v___x_6163_ = l_List_reverse___redArg(v_a_6162_);
                    return v___x_6163_;
                } else {
                    v_head_6164_ = lean_ctor_get(v_a_6161_, 0);
                    v_tail_6165_ = lean_ctor_get(v_a_6161_, 1);
                    v_isSharedCheck_6175_ = (!lean_is_exclusive(v_a_6161_)) as u8;
                    if v_isSharedCheck_6175_ == 0 {
                        v___x_6167_ = v_a_6161_;
                        v_isShared_6168_ = v_isSharedCheck_6175_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6165_);
                        lean_inc(v_head_6164_);
                        lean_dec(v_a_6161_);
                        v___x_6167_ = lean_box(0);
                        v_isShared_6168_ = v_isSharedCheck_6175_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6169_ = l_Array_contains___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__0(v___x_6160_, v_head_6164_);
                if v___x_6169_ == 0 {
                    lean_del_object(v___x_6167_);
                    lean_dec(v_head_6164_);
                    v_a_6161_ = v_tail_6165_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_6168_ == 0 {
                        lean_ctor_set(v___x_6167_, 1, v_a_6162_);
                        v___x_6172_ = v___x_6167_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6174_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6174_, 0, v_head_6164_);
                        lean_ctor_set(v_reuseFailAlloc_6174_, 1, v_a_6162_);
                        v___x_6172_ = v_reuseFailAlloc_6174_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_6161_ = v_tail_6165_;
                v_a_6162_ = v___x_6172_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1___boxed(
    mut v___x_6176_: *mut LeanObject,
    mut v_a_6177_: *mut LeanObject,
    mut v_a_6178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6179_: *mut LeanObject = core::ptr::null_mut();
    v_res_6179_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v___x_6176_, v_a_6177_, v_a_6178_);
    lean_dec_ref(v___x_6176_);
    return v_res_6179_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(
    mut v_a_6180_: *mut LeanObject,
    mut v_a_6181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6187_: u8 = 0;
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_6180_) == 0 {
                    v___x_6182_ = l_List_reverse___redArg(v_a_6181_);
                    return v___x_6182_;
                } else {
                    v_head_6183_ = lean_ctor_get(v_a_6180_, 0);
                    v_tail_6184_ = lean_ctor_get(v_a_6180_, 1);
                    v_isSharedCheck_6193_ = (!lean_is_exclusive(v_a_6180_)) as u8;
                    if v_isSharedCheck_6193_ == 0 {
                        v___x_6186_ = v_a_6180_;
                        v_isShared_6187_ = v_isSharedCheck_6193_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_6184_);
                        lean_inc(v_head_6183_);
                        lean_dec(v_a_6180_);
                        v___x_6186_ = lean_box(0);
                        v_isShared_6187_ = v_isSharedCheck_6193_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6188_ = l_Lean_Level_param___override(v_head_6183_);
                if v_isShared_6187_ == 0 {
                    lean_ctor_set(v___x_6186_, 1, v_a_6181_);
                    lean_ctor_set(v___x_6186_, 0, v___x_6188_);
                    v___x_6190_ = v___x_6186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6192_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6188_);
                    lean_ctor_set(v_reuseFailAlloc_6192_, 1, v_a_6181_);
                    v___x_6190_ = v_reuseFailAlloc_6192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6180_ = v_tail_6184_;
                v_a_6181_ = v___x_6190_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    v___x_6194_ = lean_box(0);
    v___x_6195_ = lean_unsigned_to_nat(16);
    v___x_6196_ = lean_mk_array(v___x_6195_, v___x_6194_);
    return v___x_6196_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut LeanObject = core::ptr::null_mut();
    v___x_6197_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__0);
    v___x_6198_ = lean_unsigned_to_nat(0);
    v___x_6199_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6199_, 0, v___x_6198_);
    lean_ctor_set(v___x_6199_, 1, v___x_6197_);
    return v___x_6199_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: *mut LeanObject = core::ptr::null_mut();
    v___x_6200_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0;
    v___x_6201_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__1);
    v___x_6202_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6202_, 0, v___x_6201_);
    lean_ctor_set(v___x_6202_, 1, v___x_6201_);
    lean_ctor_set(v___x_6202_, 2, v___x_6200_);
    return v___x_6202_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(
    mut v_tacticName_6203_: *mut LeanObject,
    mut v_expectedType_6204_: *mut LeanObject,
    mut v_a_6205_: *mut LeanObject,
    mut v_a_6206_: *mut LeanObject,
    mut v_a_6207_: *mut LeanObject,
    mut v_a_6208_: *mut LeanObject,
    mut v_a_6209_: *mut LeanObject,
    mut v_a_6210_: *mut LeanObject,
    mut v_a_6211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6221_: u8 = 0;
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6238_: u8 = 0;
    let mut v_inheritedTraceOptions_6239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6247_: u8 = 0;
    let mut v___x_6248_: u8 = 0;
    let mut v___y_6250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6251_: u8 = 0;
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: u8 = 0;
    let mut v___x_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: u8 = 0;
    let mut v_fileName_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6289_: u8 = 0;
    let mut v_inheritedTraceOptions_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6299_: u8 = 0;
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6305_: u8 = 0;
    let mut v_a_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: u8 = 0;
    let mut v___x_6308_: u8 = 0;
    let mut v___y_6310_: u8 = 0;
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6322_: u8 = 0;
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6329_: u8 = 0;
    let mut v_unused_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: u8 = 0;
    let mut v_isSharedCheck_6332_: u8 = 0;
    let mut v_a_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6336_: u8 = 0;
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6340_: u8 = 0;
    let mut v_a_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6344_: u8 = 0;
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_expectedType_6204_);
                v___x_6213_ = l_Lean_Meta_mkDecideProof(
                    v_expectedType_6204_,
                    v_a_6208_,
                    v_a_6209_,
                    v_a_6210_,
                    v_a_6211_,
                );
                if lean_obj_tag(v___x_6213_) == 0 {
                    v_a_6214_ = lean_ctor_get(v___x_6213_, 0);
                    lean_inc(v_a_6214_);
                    lean_dec_ref_known(v___x_6213_, 1);
                    v___x_6215_ = l_Lean_Elab_Term_getLevelNames___redArg(v_a_6207_);
                    if lean_obj_tag(v___x_6215_) == 0 {
                        v_a_6216_ = lean_ctor_get(v___x_6215_, 0);
                        lean_inc(v_a_6216_);
                        lean_dec_ref_known(v___x_6215_, 1);
                        v___x_6217_ = l_Lean_Elab_Tactic_saveState___redArg(
                            v_a_6205_, v_a_6207_, v_a_6209_, v_a_6211_,
                        );
                        if lean_obj_tag(v___x_6217_) == 0 {
                            v_a_6218_ = lean_ctor_get(v___x_6217_, 0);
                            v_isSharedCheck_6332_ = (!lean_is_exclusive(v___x_6217_)) as u8;
                            if v_isSharedCheck_6332_ == 0 {
                                v___x_6220_ = v___x_6217_;
                                v_isShared_6221_ = v_isSharedCheck_6332_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_6218_);
                                lean_dec(v___x_6217_);
                                v___x_6220_ = lean_box(0);
                                v_isShared_6221_ = v_isSharedCheck_6332_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_6216_);
                            lean_dec(v_a_6214_);
                            lean_dec_ref(v_expectedType_6204_);
                            lean_dec(v_tacticName_6203_);
                            v_a_6333_ = lean_ctor_get(v___x_6217_, 0);
                            v_isSharedCheck_6340_ = (!lean_is_exclusive(v___x_6217_)) as u8;
                            if v_isSharedCheck_6340_ == 0 {
                                v___x_6335_ = v___x_6217_;
                                v_isShared_6336_ = v_isSharedCheck_6340_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_6333_);
                                lean_dec(v___x_6217_);
                                v___x_6335_ = lean_box(0);
                                v_isShared_6336_ = v_isSharedCheck_6340_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6214_);
                        lean_dec_ref(v_expectedType_6204_);
                        lean_dec(v_tacticName_6203_);
                        v_a_6341_ = lean_ctor_get(v___x_6215_, 0);
                        v_isSharedCheck_6348_ = (!lean_is_exclusive(v___x_6215_)) as u8;
                        if v_isSharedCheck_6348_ == 0 {
                            v___x_6343_ = v___x_6215_;
                            v_isShared_6344_ = v_isSharedCheck_6348_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_6341_);
                            lean_dec(v___x_6215_);
                            v___x_6343_ = lean_box(0);
                            v_isShared_6344_ = v_isSharedCheck_6348_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_expectedType_6204_);
                    lean_dec(v_tacticName_6203_);
                    return v___x_6213_;
                }
            }
            1 => {
                v___x_6222_ = lean_st_ref_get(v_a_6211_);
                v___x_6223_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___closed__2);
                lean_inc_ref(v_expectedType_6204_);
                v___x_6224_ = l_Lean_collectLevelParams(v___x_6223_, v_expectedType_6204_);
                v_params_6225_ = lean_ctor_get(v___x_6224_, 2);
                lean_inc_ref(v_params_6225_);
                lean_dec_ref(v___x_6224_);
                v_fileName_6226_ = lean_ctor_get(v_a_6210_, 0);
                v_fileMap_6227_ = lean_ctor_get(v_a_6210_, 1);
                v_options_6228_ = lean_ctor_get(v_a_6210_, 2);
                v_currRecDepth_6229_ = lean_ctor_get(v_a_6210_, 3);
                v_ref_6230_ = lean_ctor_get(v_a_6210_, 5);
                v_currNamespace_6231_ = lean_ctor_get(v_a_6210_, 6);
                v_openDecls_6232_ = lean_ctor_get(v_a_6210_, 7);
                v_initHeartbeats_6233_ = lean_ctor_get(v_a_6210_, 8);
                v_maxHeartbeats_6234_ = lean_ctor_get(v_a_6210_, 9);
                v_quotContext_6235_ = lean_ctor_get(v_a_6210_, 10);
                v_currMacroScope_6236_ = lean_ctor_get(v_a_6210_, 11);
                v_cancelTk_x3f_6237_ = lean_ctor_get(v_a_6210_, 12);
                v_suppressElabErrors_6238_ = lean_ctor_get_uint8(
                    v_a_6210_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6239_ = lean_ctor_get(v_a_6210_, 13);
                v_env_6240_ = lean_ctor_get(v___x_6222_, 0);
                lean_inc_ref(v_env_6240_);
                lean_dec(v___x_6222_);
                v___x_6241_ = l_Lean_Expr_appFn_x21(v_a_6214_);
                v___x_6242_ = l_Lean_Expr_appArg_x21(v___x_6241_);
                lean_dec_ref(v___x_6241_);
                v___x_6243_ = l_List_reverse___redArg(v_a_6216_);
                v___x_6244_ = lean_box(0);
                v___x_6245_ = l_List_filterTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__1(v_params_6225_, v___x_6243_, v___x_6244_);
                lean_dec_ref(v_params_6225_);
                v___x_6246_ = lean_box(0);
                v___x_6247_ = 1;
                v___x_6248_ = 0;
                v___x_6273_ = l_Lean_Elab_async;
                lean_inc_ref(v_options_6228_);
                v___x_6274_ = l_Lean_Option_set___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__0(v_options_6228_, v___x_6273_, v___x_6248_);
                v___x_6275_ = l_Lean_diagnostics;
                v___x_6276_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0_spec__1_spec__3(v___x_6274_, v___x_6275_);
                v___x_6331_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_6240_);
                lean_dec_ref(v_env_6240_);
                if v___x_6331_ == 0 {
                    if v___x_6276_ == 0 {
                        v_fileName_6278_ = v_fileName_6226_;
                        v_fileMap_6279_ = v_fileMap_6227_;
                        v_currRecDepth_6280_ = v_currRecDepth_6229_;
                        v_ref_6281_ = v_ref_6230_;
                        v_currNamespace_6282_ = v_currNamespace_6231_;
                        v_openDecls_6283_ = v_openDecls_6232_;
                        v_initHeartbeats_6284_ = v_initHeartbeats_6233_;
                        v_maxHeartbeats_6285_ = v_maxHeartbeats_6234_;
                        v_quotContext_6286_ = v_quotContext_6235_;
                        v_currMacroScope_6287_ = v_currMacroScope_6236_;
                        v_cancelTk_x3f_6288_ = v_cancelTk_x3f_6237_;
                        v_suppressElabErrors_6289_ = v_suppressElabErrors_6238_;
                        v_inheritedTraceOptions_6290_ = v_inheritedTraceOptions_6239_;
                        v___y_6291_ = v_a_6211_;
                        state = 6;
                        continue;
                    } else {
                        v___y_6310_ = v___x_6331_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___y_6310_ = v___x_6276_;
                    state = 9;
                    continue;
                }
            }
            2 => {
                if v___y_6251_ == 0 {
                    lean_del_object(v___x_6220_);
                    v___x_6252_ = l_Lean_Elab_Tactic_SavedState_restore___redArg(
                        v_a_6218_,
                        v___y_6251_,
                        v_a_6205_,
                        v_a_6206_,
                        v_a_6207_,
                        v_a_6208_,
                        v_a_6209_,
                        v_a_6210_,
                        v_a_6211_,
                    );
                    if lean_obj_tag(v___x_6252_) == 0 {
                        lean_dec_ref_known(v___x_6252_, 1);
                        v___x_6253_ = 1;
                        v___x_6254_ = lean_box((v___x_6248_) as usize);
                        v___x_6255_ = lean_box((v___x_6253_) as usize);
                        lean_inc_ref(v_expectedType_6204_);
                        v___f_6256_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 6);
                        lean_closure_set(v___f_6256_, 0, v___x_6242_);
                        lean_closure_set(v___f_6256_, 1, v_tacticName_6203_);
                        lean_closure_set(v___f_6256_, 2, v_expectedType_6204_);
                        lean_closure_set(v___f_6256_, 3, v___x_6254_);
                        lean_closure_set(v___f_6256_, 4, v___y_6250_);
                        lean_closure_set(v___f_6256_, 5, v___x_6255_);
                        v___x_6257_ = lean_unsigned_to_nat(1);
                        v___x_6258_ = lean_mk_empty_array_with_capacity(v___x_6257_);
                        v___x_6259_ = lean_array_push(v___x_6258_, v_expectedType_6204_);
                        v___x_6260_ = l_Lean_MessageData_ofLazyM(v___f_6256_, v___x_6259_);
                        v___x_6261_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_6260_, v_a_6208_, v_a_6209_, v_a_6210_, v_a_6211_);
                        return v___x_6261_;
                    } else {
                        lean_dec_ref(v___y_6250_);
                        lean_dec_ref(v___x_6242_);
                        lean_dec_ref(v_expectedType_6204_);
                        lean_dec(v_tacticName_6203_);
                        v_a_6262_ = lean_ctor_get(v___x_6252_, 0);
                        v_isSharedCheck_6269_ = (!lean_is_exclusive(v___x_6252_)) as u8;
                        if v_isSharedCheck_6269_ == 0 {
                            v___x_6264_ = v___x_6252_;
                            v_isShared_6265_ = v_isSharedCheck_6269_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6262_);
                            lean_dec(v___x_6252_);
                            v___x_6264_ = lean_box(0);
                            v_isShared_6265_ = v_isSharedCheck_6269_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_6242_);
                    lean_dec(v_a_6218_);
                    lean_dec_ref(v_expectedType_6204_);
                    lean_dec(v_tacticName_6203_);
                    if v_isShared_6221_ == 0 {
                        lean_ctor_set_tag(v___x_6220_, 1);
                        lean_ctor_set(v___x_6220_, 0, v___y_6250_);
                        v___x_6271_ = v___x_6220_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6272_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6272_, 0, v___y_6250_);
                        v___x_6271_ = v_reuseFailAlloc_6272_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6265_ == 0 {
                    v___x_6267_ = v___x_6264_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6267_;
            }
            5 => {
                return v___x_6271_;
            }
            6 => {
                v___x_6292_ = l_Lean_maxRecDepth;
                v___x_6293_ = l_Lean_Option_get___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__1(v___x_6274_, v___x_6292_);
                lean_inc_ref(v_inheritedTraceOptions_6290_);
                lean_inc(v_cancelTk_x3f_6288_);
                lean_inc(v_currMacroScope_6287_);
                lean_inc(v_quotContext_6286_);
                lean_inc(v_maxHeartbeats_6285_);
                lean_inc(v_initHeartbeats_6284_);
                lean_inc(v_openDecls_6283_);
                lean_inc(v_currNamespace_6282_);
                lean_inc(v_ref_6281_);
                lean_inc(v_currRecDepth_6280_);
                lean_inc_ref(v_fileMap_6279_);
                lean_inc_ref(v_fileName_6278_);
                v___x_6294_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_6294_, 0, v_fileName_6278_);
                lean_ctor_set(v___x_6294_, 1, v_fileMap_6279_);
                lean_ctor_set(v___x_6294_, 2, v___x_6274_);
                lean_ctor_set(v___x_6294_, 3, v_currRecDepth_6280_);
                lean_ctor_set(v___x_6294_, 4, v___x_6293_);
                lean_ctor_set(v___x_6294_, 5, v_ref_6281_);
                lean_ctor_set(v___x_6294_, 6, v_currNamespace_6282_);
                lean_ctor_set(v___x_6294_, 7, v_openDecls_6283_);
                lean_ctor_set(v___x_6294_, 8, v_initHeartbeats_6284_);
                lean_ctor_set(v___x_6294_, 9, v_maxHeartbeats_6285_);
                lean_ctor_set(v___x_6294_, 10, v_quotContext_6286_);
                lean_ctor_set(v___x_6294_, 11, v_currMacroScope_6287_);
                lean_ctor_set(v___x_6294_, 12, v_cancelTk_x3f_6288_);
                lean_ctor_set(v___x_6294_, 13, v_inheritedTraceOptions_6290_);
                lean_ctor_set_uint8(
                    v___x_6294_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___x_6276_,
                );
                lean_ctor_set_uint8(
                    v___x_6294_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6289_,
                );
                lean_inc_ref(v_expectedType_6204_);
                lean_inc(v___x_6245_);
                v___x_6295_ = l_Lean_Meta_mkAuxLemma(
                    v___x_6245_,
                    v_expectedType_6204_,
                    v_a_6214_,
                    v___x_6246_,
                    v___x_6247_,
                    v___x_6248_,
                    v___x_6248_,
                    v___x_6248_,
                    v_a_6208_,
                    v_a_6209_,
                    v___x_6294_,
                    v___y_6291_,
                );
                lean_dec_ref_known(v___x_6294_, 14);
                if lean_obj_tag(v___x_6295_) == 0 {
                    lean_dec_ref(v___x_6242_);
                    lean_del_object(v___x_6220_);
                    lean_dec(v_a_6218_);
                    lean_dec_ref(v_expectedType_6204_);
                    lean_dec(v_tacticName_6203_);
                    v_a_6296_ = lean_ctor_get(v___x_6295_, 0);
                    v_isSharedCheck_6305_ = (!lean_is_exclusive(v___x_6295_)) as u8;
                    if v_isSharedCheck_6305_ == 0 {
                        v___x_6298_ = v___x_6295_;
                        v_isShared_6299_ = v_isSharedCheck_6305_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6296_);
                        lean_dec(v___x_6295_);
                        v___x_6298_ = lean_box(0);
                        v_isShared_6299_ = v_isSharedCheck_6305_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6245_);
                    v_a_6306_ = lean_ctor_get(v___x_6295_, 0);
                    lean_inc(v_a_6306_);
                    lean_dec_ref_known(v___x_6295_, 1);
                    v___x_6307_ = l_Lean_Exception_isInterrupt(v_a_6306_);
                    if v___x_6307_ == 0 {
                        lean_inc(v_a_6306_);
                        v___x_6308_ = l_Lean_Exception_isRuntime(v_a_6306_);
                        v___y_6250_ = v_a_6306_;
                        v___y_6251_ = v___x_6308_;
                        state = 2;
                        continue;
                    } else {
                        v___y_6250_ = v_a_6306_;
                        v___y_6251_ = v___x_6307_;
                        state = 2;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6300_ = l_List_mapTR_loop___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel_spec__2(v___x_6245_, v___x_6244_);
                v___x_6301_ = l_Lean_mkConst(v_a_6296_, v___x_6300_);
                if v_isShared_6299_ == 0 {
                    lean_ctor_set(v___x_6298_, 0, v___x_6301_);
                    v___x_6303_ = v___x_6298_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6304_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6304_, 0, v___x_6301_);
                    v___x_6303_ = v_reuseFailAlloc_6304_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6303_;
            }
            9 => {
                if v___y_6310_ == 0 {
                    v___x_6311_ = lean_st_ref_take(v_a_6211_);
                    v_env_6312_ = lean_ctor_get(v___x_6311_, 0);
                    v_nextMacroScope_6313_ = lean_ctor_get(v___x_6311_, 1);
                    v_ngen_6314_ = lean_ctor_get(v___x_6311_, 2);
                    v_auxDeclNGen_6315_ = lean_ctor_get(v___x_6311_, 3);
                    v_traceState_6316_ = lean_ctor_get(v___x_6311_, 4);
                    v_messages_6317_ = lean_ctor_get(v___x_6311_, 6);
                    v_infoState_6318_ = lean_ctor_get(v___x_6311_, 7);
                    v_snapshotTasks_6319_ = lean_ctor_get(v___x_6311_, 8);
                    v_isSharedCheck_6329_ = (!lean_is_exclusive(v___x_6311_)) as u8;
                    if v_isSharedCheck_6329_ == 0 {
                        v_unused_6330_ = lean_ctor_get(v___x_6311_, 5);
                        lean_dec(v_unused_6330_);
                        v___x_6321_ = v___x_6311_;
                        v_isShared_6322_ = v_isSharedCheck_6329_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_6319_);
                        lean_inc(v_infoState_6318_);
                        lean_inc(v_messages_6317_);
                        lean_inc(v_traceState_6316_);
                        lean_inc(v_auxDeclNGen_6315_);
                        lean_inc(v_ngen_6314_);
                        lean_inc(v_nextMacroScope_6313_);
                        lean_inc(v_env_6312_);
                        lean_dec(v___x_6311_);
                        v___x_6321_ = lean_box(0);
                        v_isShared_6322_ = v_isSharedCheck_6329_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_fileName_6278_ = v_fileName_6226_;
                    v_fileMap_6279_ = v_fileMap_6227_;
                    v_currRecDepth_6280_ = v_currRecDepth_6229_;
                    v_ref_6281_ = v_ref_6230_;
                    v_currNamespace_6282_ = v_currNamespace_6231_;
                    v_openDecls_6283_ = v_openDecls_6232_;
                    v_initHeartbeats_6284_ = v_initHeartbeats_6233_;
                    v_maxHeartbeats_6285_ = v_maxHeartbeats_6234_;
                    v_quotContext_6286_ = v_quotContext_6235_;
                    v_currMacroScope_6287_ = v_currMacroScope_6236_;
                    v_cancelTk_x3f_6288_ = v_cancelTk_x3f_6237_;
                    v_suppressElabErrors_6289_ = v_suppressElabErrors_6238_;
                    v_inheritedTraceOptions_6290_ = v_inheritedTraceOptions_6239_;
                    v___y_6291_ = v_a_6211_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                v___x_6323_ = l_Lean_Kernel_enableDiag(v_env_6312_, v___x_6276_);
                v___x_6324_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__6);
                if v_isShared_6322_ == 0 {
                    lean_ctor_set(v___x_6321_, 5, v___x_6324_);
                    lean_ctor_set(v___x_6321_, 0, v___x_6323_);
                    v___x_6326_ = v___x_6321_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6328_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 0, v___x_6323_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 1, v_nextMacroScope_6313_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 2, v_ngen_6314_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 3, v_auxDeclNGen_6315_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 4, v_traceState_6316_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 5, v___x_6324_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 6, v_messages_6317_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 7, v_infoState_6318_);
                    lean_ctor_set(v_reuseFailAlloc_6328_, 8, v_snapshotTasks_6319_);
                    v___x_6326_ = v_reuseFailAlloc_6328_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_6327_ = lean_st_ref_set(v_a_6211_, v___x_6326_);
                v_fileName_6278_ = v_fileName_6226_;
                v_fileMap_6279_ = v_fileMap_6227_;
                v_currRecDepth_6280_ = v_currRecDepth_6229_;
                v_ref_6281_ = v_ref_6230_;
                v_currNamespace_6282_ = v_currNamespace_6231_;
                v_openDecls_6283_ = v_openDecls_6232_;
                v_initHeartbeats_6284_ = v_initHeartbeats_6233_;
                v_maxHeartbeats_6285_ = v_maxHeartbeats_6234_;
                v_quotContext_6286_ = v_quotContext_6235_;
                v_currMacroScope_6287_ = v_currMacroScope_6236_;
                v_cancelTk_x3f_6288_ = v_cancelTk_x3f_6237_;
                v_suppressElabErrors_6289_ = v_suppressElabErrors_6238_;
                v_inheritedTraceOptions_6290_ = v_inheritedTraceOptions_6239_;
                v___y_6291_ = v_a_6211_;
                state = 6;
                continue;
            }
            12 => {
                if v_isShared_6336_ == 0 {
                    v___x_6338_ = v___x_6335_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6339_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6339_, 0, v_a_6333_);
                    v___x_6338_ = v_reuseFailAlloc_6339_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6338_;
            }
            14 => {
                if v_isShared_6344_ == 0 {
                    v___x_6346_ = v___x_6343_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6347_, 0, v_a_6341_);
                    v___x_6346_ = v_reuseFailAlloc_6347_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg___boxed(
    mut v_tacticName_6349_: *mut LeanObject,
    mut v_expectedType_6350_: *mut LeanObject,
    mut v_a_6351_: *mut LeanObject,
    mut v_a_6352_: *mut LeanObject,
    mut v_a_6353_: *mut LeanObject,
    mut v_a_6354_: *mut LeanObject,
    mut v_a_6355_: *mut LeanObject,
    mut v_a_6356_: *mut LeanObject,
    mut v_a_6357_: *mut LeanObject,
    mut v_a_6358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6359_: *mut LeanObject = core::ptr::null_mut();
    v_res_6359_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(
            v_tacticName_6349_,
            v_expectedType_6350_,
            v_a_6351_,
            v_a_6352_,
            v_a_6353_,
            v_a_6354_,
            v_a_6355_,
            v_a_6356_,
            v_a_6357_,
        );
    lean_dec(v_a_6357_);
    lean_dec_ref(v_a_6356_);
    lean_dec(v_a_6355_);
    lean_dec_ref(v_a_6354_);
    lean_dec(v_a_6353_);
    lean_dec_ref(v_a_6352_);
    lean_dec(v_a_6351_);
    return v_res_6359_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(
    mut v_tacticName_6360_: *mut LeanObject,
    mut v_expectedType_6361_: *mut LeanObject,
    mut v_a_6362_: *mut LeanObject,
    mut v_a_6363_: *mut LeanObject,
    mut v_a_6364_: *mut LeanObject,
    mut v_a_6365_: *mut LeanObject,
    mut v_a_6366_: *mut LeanObject,
    mut v_a_6367_: *mut LeanObject,
    mut v_a_6368_: *mut LeanObject,
    mut v_a_6369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    v___x_6371_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(
            v_tacticName_6360_,
            v_expectedType_6361_,
            v_a_6363_,
            v_a_6364_,
            v_a_6365_,
            v_a_6366_,
            v_a_6367_,
            v_a_6368_,
            v_a_6369_,
        );
    return v___x_6371_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___boxed(
    mut v_tacticName_6372_: *mut LeanObject,
    mut v_expectedType_6373_: *mut LeanObject,
    mut v_a_6374_: *mut LeanObject,
    mut v_a_6375_: *mut LeanObject,
    mut v_a_6376_: *mut LeanObject,
    mut v_a_6377_: *mut LeanObject,
    mut v_a_6378_: *mut LeanObject,
    mut v_a_6379_: *mut LeanObject,
    mut v_a_6380_: *mut LeanObject,
    mut v_a_6381_: *mut LeanObject,
    mut v_a_6382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6383_: *mut LeanObject = core::ptr::null_mut();
    v_res_6383_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel(
        v_tacticName_6372_,
        v_expectedType_6373_,
        v_a_6374_,
        v_a_6375_,
        v_a_6376_,
        v_a_6377_,
        v_a_6378_,
        v_a_6379_,
        v_a_6380_,
        v_a_6381_,
    );
    lean_dec(v_a_6381_);
    lean_dec_ref(v_a_6380_);
    lean_dec(v_a_6379_);
    lean_dec_ref(v_a_6378_);
    lean_dec(v_a_6377_);
    lean_dec_ref(v_a_6376_);
    lean_dec(v_a_6375_);
    lean_dec_ref(v_a_6374_);
    return v_res_6383_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    v___x_6385_ = l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__0;
    v___x_6386_ = l_Lean_stringToMessageData(v___x_6385_);
    return v___x_6386_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecideCore___lam__0(
    mut v_native_6387_: u8,
    mut v_kernel_6388_: u8,
    mut v_tacticName_6389_: *mut LeanObject,
    mut v_expectedType_6390_: *mut LeanObject,
    mut v_x_6391_: *mut LeanObject,
    mut v___y_6392_: *mut LeanObject,
    mut v___y_6393_: *mut LeanObject,
    mut v___y_6394_: *mut LeanObject,
    mut v___y_6395_: *mut LeanObject,
    mut v___y_6396_: *mut LeanObject,
    mut v___y_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6426_: u8 = 0;
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_kernel_6388_ == 0 {
                    v___y_6402_ = v___y_6392_;
                    v___y_6403_ = v___y_6393_;
                    v___y_6404_ = v___y_6394_;
                    v___y_6405_ = v___y_6395_;
                    v___y_6406_ = v___y_6396_;
                    v___y_6407_ = v___y_6397_;
                    v___y_6408_ = v___y_6398_;
                    v___y_6409_ = v___y_6399_;
                    state = 1;
                    continue;
                } else {
                    if v_native_6387_ == 0 {
                        v___y_6402_ = v___y_6392_;
                        v___y_6403_ = v___y_6393_;
                        v___y_6404_ = v___y_6394_;
                        v___y_6405_ = v___y_6395_;
                        v___y_6406_ = v___y_6396_;
                        v___y_6407_ = v___y_6397_;
                        v___y_6408_ = v___y_6398_;
                        v___y_6409_ = v___y_6399_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_expectedType_6390_);
                        v___x_6417_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4_once
                            ),
                            _init_l_Lean_Elab_Tactic_elabNativeDecideCore___closed__4,
                        );
                        v___x_6418_ = l_Lean_MessageData_ofName(v_tacticName_6389_);
                        v___x_6419_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6419_, 0, v___x_6417_);
                        lean_ctor_set(v___x_6419_, 1, v___x_6418_);
                        v___x_6420_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1_once
                            ),
                            _init_l_Lean_Elab_Tactic_evalDecideCore___lam__0___closed__1,
                        );
                        v___x_6421_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_6421_, 0, v___x_6419_);
                        lean_ctor_set(v___x_6421_, 1, v___x_6420_);
                        v___x_6422_ = l_Lean_throwError___at___00Lean_Elab_Tactic_elabNativeDecideCore_spec__0___redArg(v___x_6421_, v___y_6396_, v___y_6397_, v___y_6398_, v___y_6399_);
                        v_a_6423_ = lean_ctor_get(v___x_6422_, 0);
                        v_isSharedCheck_6430_ = (!lean_is_exclusive(v___x_6422_)) as u8;
                        if v_isSharedCheck_6430_ == 0 {
                            v___x_6425_ = v___x_6422_;
                            v_isShared_6426_ = v_isSharedCheck_6430_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_6423_);
                            lean_dec(v___x_6422_);
                            v___x_6425_ = lean_box(0);
                            v_isShared_6426_ = v_isSharedCheck_6430_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6410_ =
                    l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide(
                        v_expectedType_6390_,
                        v___y_6404_,
                        v___y_6405_,
                        v___y_6406_,
                        v___y_6407_,
                        v___y_6408_,
                        v___y_6409_,
                    );
                if lean_obj_tag(v___x_6410_) == 0 {
                    if v_native_6387_ == 0 {
                        if v_kernel_6388_ == 0 {
                            v_a_6411_ = lean_ctor_get(v___x_6410_, 0);
                            lean_inc(v_a_6411_);
                            lean_dec_ref_known(v___x_6410_, 1);
                            v___x_6412_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doElab___redArg(v_tacticName_6389_, v_a_6411_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_);
                            return v___x_6412_;
                        } else {
                            v_a_6413_ = lean_ctor_get(v___x_6410_, 0);
                            lean_inc(v_a_6413_);
                            lean_dec_ref_known(v___x_6410_, 1);
                            v___x_6414_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_doKernel___redArg(v_tacticName_6389_, v_a_6413_, v___y_6403_, v___y_6404_, v___y_6405_, v___y_6406_, v___y_6407_, v___y_6408_, v___y_6409_);
                            return v___x_6414_;
                        }
                    } else {
                        v_a_6415_ = lean_ctor_get(v___x_6410_, 0);
                        lean_inc(v_a_6415_);
                        lean_dec_ref_known(v___x_6410_, 1);
                        v___x_6416_ = l_Lean_Elab_Tactic_elabNativeDecideCore(
                            v_tacticName_6389_,
                            v_a_6415_,
                            v___y_6402_,
                            v___y_6403_,
                            v___y_6404_,
                            v___y_6405_,
                            v___y_6406_,
                            v___y_6407_,
                            v___y_6408_,
                            v___y_6409_,
                        );
                        return v___x_6416_;
                    }
                } else {
                    lean_dec(v_tacticName_6389_);
                    return v___x_6410_;
                }
            }
            2 => {
                if v_isShared_6426_ == 0 {
                    v___x_6428_ = v___x_6425_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6429_, 0, v_a_6423_);
                    v___x_6428_ = v_reuseFailAlloc_6429_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed(
    mut v_native_6431_: *mut LeanObject,
    mut v_kernel_6432_: *mut LeanObject,
    mut v_tacticName_6433_: *mut LeanObject,
    mut v_expectedType_6434_: *mut LeanObject,
    mut v_x_6435_: *mut LeanObject,
    mut v___y_6436_: *mut LeanObject,
    mut v___y_6437_: *mut LeanObject,
    mut v___y_6438_: *mut LeanObject,
    mut v___y_6439_: *mut LeanObject,
    mut v___y_6440_: *mut LeanObject,
    mut v___y_6441_: *mut LeanObject,
    mut v___y_6442_: *mut LeanObject,
    mut v___y_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_native_boxed_6445_: u8 = 0;
    let mut v_kernel_boxed_6446_: u8 = 0;
    let mut v_res_6447_: *mut LeanObject = core::ptr::null_mut();
    v_native_boxed_6445_ = (lean_unbox(v_native_6431_) as u8);
    v_kernel_boxed_6446_ = (lean_unbox(v_kernel_6432_) as u8);
    v_res_6447_ = l_Lean_Elab_Tactic_evalDecideCore___lam__0(
        v_native_boxed_6445_,
        v_kernel_boxed_6446_,
        v_tacticName_6433_,
        v_expectedType_6434_,
        v_x_6435_,
        v___y_6436_,
        v___y_6437_,
        v___y_6438_,
        v___y_6439_,
        v___y_6440_,
        v___y_6441_,
        v___y_6442_,
        v___y_6443_,
    );
    lean_dec(v___y_6443_);
    lean_dec_ref(v___y_6442_);
    lean_dec(v___y_6441_);
    lean_dec_ref(v___y_6440_);
    lean_dec(v___y_6439_);
    lean_dec_ref(v___y_6438_);
    lean_dec(v___y_6437_);
    lean_dec_ref(v___y_6436_);
    lean_dec(v_x_6435_);
    return v_res_6447_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecideCore___lam__1(
    mut v_revert_6448_: u8,
    mut v___y_6449_: *mut LeanObject,
    mut v___y_6450_: *mut LeanObject,
    mut v___y_6451_: *mut LeanObject,
    mut v___y_6452_: *mut LeanObject,
    mut v___y_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
    mut v___y_6455_: *mut LeanObject,
    mut v___y_6456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: u8 = 0;
    let mut v___x_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6473_: u8 = 0;
    let mut v___x_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6479_: u8 = 0;
    let mut v_unused_6480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6484_: u8 = 0;
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6488_: u8 = 0;
    let mut v_a_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6492_: u8 = 0;
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6496_: u8 = 0;
    let mut v_a_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6504_: u8 = 0;
    let mut v_a_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6508_: u8 = 0;
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6512_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6458_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_6450_,
                    v___y_6453_,
                    v___y_6454_,
                    v___y_6455_,
                    v___y_6456_,
                );
                if lean_obj_tag(v___x_6458_) == 0 {
                    v_a_6459_ = lean_ctor_get(v___x_6458_, 0);
                    lean_inc(v_a_6459_);
                    lean_dec_ref_known(v___x_6458_, 1);
                    v___x_6460_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose___lam__1___closed__0;
                    v___x_6461_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(
                        v_a_6459_,
                        v___x_6460_,
                        v_revert_6448_,
                        v___y_6453_,
                        v___y_6454_,
                        v___y_6455_,
                        v___y_6456_,
                    );
                    if lean_obj_tag(v___x_6461_) == 0 {
                        v_a_6462_ = lean_ctor_get(v___x_6461_, 0);
                        lean_inc_n(v_a_6462_, 2);
                        lean_dec_ref_known(v___x_6461_, 1);
                        v___x_6463_ = l_Lean_MVarId_getDecl(
                            v_a_6462_,
                            v___y_6453_,
                            v___y_6454_,
                            v___y_6455_,
                            v___y_6456_,
                        );
                        if lean_obj_tag(v___x_6463_) == 0 {
                            v_a_6464_ = lean_ctor_get(v___x_6463_, 0);
                            lean_inc(v_a_6464_);
                            lean_dec_ref_known(v___x_6463_, 1);
                            v_lctx_6465_ = lean_ctor_get(v_a_6464_, 1);
                            lean_inc_ref(v_lctx_6465_);
                            lean_dec(v_a_6464_);
                            v___x_6466_ = l_Lean_LocalContext_getFVarIds(v_lctx_6465_);
                            lean_dec_ref(v_lctx_6465_);
                            v___x_6467_ = 0;
                            v___x_6468_ = l_Lean_MVarId_revert(
                                v_a_6462_,
                                v___x_6466_,
                                v___x_6467_,
                                v_revert_6448_,
                                v___y_6453_,
                                v___y_6454_,
                                v___y_6455_,
                                v___y_6456_,
                            );
                            if lean_obj_tag(v___x_6468_) == 0 {
                                v_a_6469_ = lean_ctor_get(v___x_6468_, 0);
                                lean_inc(v_a_6469_);
                                lean_dec_ref_known(v___x_6468_, 1);
                                v_snd_6470_ = lean_ctor_get(v_a_6469_, 1);
                                v_isSharedCheck_6479_ = (!lean_is_exclusive(v_a_6469_)) as u8;
                                if v_isSharedCheck_6479_ == 0 {
                                    v_unused_6480_ = lean_ctor_get(v_a_6469_, 0);
                                    lean_dec(v_unused_6480_);
                                    v___x_6472_ = v_a_6469_;
                                    v_isShared_6473_ = v_isSharedCheck_6479_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_snd_6470_);
                                    lean_dec(v_a_6469_);
                                    v___x_6472_ = lean_box(0);
                                    v_isShared_6473_ = v_isSharedCheck_6479_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_6481_ = lean_ctor_get(v___x_6468_, 0);
                                v_isSharedCheck_6488_ = (!lean_is_exclusive(v___x_6468_)) as u8;
                                if v_isSharedCheck_6488_ == 0 {
                                    v___x_6483_ = v___x_6468_;
                                    v_isShared_6484_ = v_isSharedCheck_6488_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6481_);
                                    lean_dec(v___x_6468_);
                                    v___x_6483_ = lean_box(0);
                                    v_isShared_6484_ = v_isSharedCheck_6488_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6462_);
                            v_a_6489_ = lean_ctor_get(v___x_6463_, 0);
                            v_isSharedCheck_6496_ = (!lean_is_exclusive(v___x_6463_)) as u8;
                            if v_isSharedCheck_6496_ == 0 {
                                v___x_6491_ = v___x_6463_;
                                v_isShared_6492_ = v_isSharedCheck_6496_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6489_);
                                lean_dec(v___x_6463_);
                                v___x_6491_ = lean_box(0);
                                v_isShared_6492_ = v_isSharedCheck_6496_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        v_a_6497_ = lean_ctor_get(v___x_6461_, 0);
                        v_isSharedCheck_6504_ = (!lean_is_exclusive(v___x_6461_)) as u8;
                        if v_isSharedCheck_6504_ == 0 {
                            v___x_6499_ = v___x_6461_;
                            v_isShared_6500_ = v_isSharedCheck_6504_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_6497_);
                            lean_dec(v___x_6461_);
                            v___x_6499_ = lean_box(0);
                            v_isShared_6500_ = v_isSharedCheck_6504_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_6505_ = lean_ctor_get(v___x_6458_, 0);
                    v_isSharedCheck_6512_ = (!lean_is_exclusive(v___x_6458_)) as u8;
                    if v_isSharedCheck_6512_ == 0 {
                        v___x_6507_ = v___x_6458_;
                        v_isShared_6508_ = v_isSharedCheck_6512_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_6505_);
                        lean_dec(v___x_6458_);
                        v___x_6507_ = lean_box(0);
                        v_isShared_6508_ = v_isSharedCheck_6512_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6474_ = lean_box(0);
                if v_isShared_6473_ == 0 {
                    lean_ctor_set_tag(v___x_6472_, 1);
                    lean_ctor_set(v___x_6472_, 1, v___x_6474_);
                    lean_ctor_set(v___x_6472_, 0, v_snd_6470_);
                    v___x_6476_ = v___x_6472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6478_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6478_, 0, v_snd_6470_);
                    lean_ctor_set(v_reuseFailAlloc_6478_, 1, v___x_6474_);
                    v___x_6476_ = v_reuseFailAlloc_6478_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6477_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                    v___x_6476_,
                    v___y_6450_,
                    v___y_6453_,
                    v___y_6454_,
                    v___y_6455_,
                    v___y_6456_,
                );
                return v___x_6477_;
            }
            3 => {
                if v_isShared_6484_ == 0 {
                    v___x_6486_ = v___x_6483_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6487_, 0, v_a_6481_);
                    v___x_6486_ = v_reuseFailAlloc_6487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6486_;
            }
            5 => {
                if v_isShared_6492_ == 0 {
                    v___x_6494_ = v___x_6491_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6495_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_a_6489_);
                    v___x_6494_ = v_reuseFailAlloc_6495_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6494_;
            }
            7 => {
                if v_isShared_6500_ == 0 {
                    v___x_6502_ = v___x_6499_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6503_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6503_, 0, v_a_6497_);
                    v___x_6502_ = v_reuseFailAlloc_6503_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6502_;
            }
            9 => {
                if v_isShared_6508_ == 0 {
                    v___x_6510_ = v___x_6507_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6511_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6511_, 0, v_a_6505_);
                    v___x_6510_ = v_reuseFailAlloc_6511_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed(
    mut v_revert_6513_: *mut LeanObject,
    mut v___y_6514_: *mut LeanObject,
    mut v___y_6515_: *mut LeanObject,
    mut v___y_6516_: *mut LeanObject,
    mut v___y_6517_: *mut LeanObject,
    mut v___y_6518_: *mut LeanObject,
    mut v___y_6519_: *mut LeanObject,
    mut v___y_6520_: *mut LeanObject,
    mut v___y_6521_: *mut LeanObject,
    mut v___y_6522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_revert_boxed_6523_: u8 = 0;
    let mut v_res_6524_: *mut LeanObject = core::ptr::null_mut();
    v_revert_boxed_6523_ = (lean_unbox(v_revert_6513_) as u8);
    v_res_6524_ = l_Lean_Elab_Tactic_evalDecideCore___lam__1(
        v_revert_boxed_6523_,
        v___y_6514_,
        v___y_6515_,
        v___y_6516_,
        v___y_6517_,
        v___y_6518_,
        v___y_6519_,
        v___y_6520_,
        v___y_6521_,
    );
    lean_dec(v___y_6521_);
    lean_dec_ref(v___y_6520_);
    lean_dec(v___y_6519_);
    lean_dec_ref(v___y_6518_);
    lean_dec(v___y_6517_);
    lean_dec_ref(v___y_6516_);
    lean_dec(v___y_6515_);
    lean_dec_ref(v___y_6514_);
    return v_res_6524_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecideCore(
    mut v_tacticName_6525_: *mut LeanObject,
    mut v_cfg_6526_: *mut LeanObject,
    mut v_a_6527_: *mut LeanObject,
    mut v_a_6528_: *mut LeanObject,
    mut v_a_6529_: *mut LeanObject,
    mut v_a_6530_: *mut LeanObject,
    mut v_a_6531_: *mut LeanObject,
    mut v_a_6532_: *mut LeanObject,
    mut v_a_6533_: *mut LeanObject,
    mut v_a_6534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kernel_6536_: u8 = 0;
    let mut v_native_6537_: u8 = 0;
    let mut v_revert_6538_: u8 = 0;
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: u8 = 0;
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_kernel_6536_ = lean_ctor_get_uint8(v_cfg_6526_, 0 as u32);
                v_native_6537_ = lean_ctor_get_uint8(v_cfg_6526_, 1 as u32);
                v_revert_6538_ = lean_ctor_get_uint8(v_cfg_6526_, 3 as u32);
                v___x_6539_ = lean_box((v_native_6537_) as usize);
                v___x_6540_ = lean_box((v_kernel_6536_) as usize);
                lean_inc(v_tacticName_6525_);
                v___f_6541_ = lean_alloc_closure(
                    l_Lean_Elab_Tactic_evalDecideCore___lam__0___boxed as *mut core::ffi::c_void,
                    14,
                    3,
                );
                lean_closure_set(v___f_6541_, 0, v___x_6539_);
                lean_closure_set(v___f_6541_, 1, v___x_6540_);
                lean_closure_set(v___f_6541_, 2, v_tacticName_6525_);
                if v_revert_6538_ == 0 {
                    v___y_6543_ = v_a_6527_;
                    v___y_6544_ = v_a_6528_;
                    v___y_6545_ = v_a_6529_;
                    v___y_6546_ = v_a_6530_;
                    v___y_6547_ = v_a_6531_;
                    v___y_6548_ = v_a_6532_;
                    v___y_6549_ = v_a_6533_;
                    v___y_6550_ = v_a_6534_;
                    state = 1;
                    continue;
                } else {
                    v___x_6553_ = lean_box((v_revert_6538_) as usize);
                    v___f_6554_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalDecideCore___lam__1___boxed
                            as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___f_6554_, 0, v___x_6553_);
                    v___x_6555_ = l_Lean_Elab_Tactic_withMainContext___redArg(
                        v___f_6554_,
                        v_a_6527_,
                        v_a_6528_,
                        v_a_6529_,
                        v_a_6530_,
                        v_a_6531_,
                        v_a_6532_,
                        v_a_6533_,
                        v_a_6534_,
                    );
                    if lean_obj_tag(v___x_6555_) == 0 {
                        lean_dec_ref_known(v___x_6555_, 1);
                        v___y_6543_ = v_a_6527_;
                        v___y_6544_ = v_a_6528_;
                        v___y_6545_ = v_a_6529_;
                        v___y_6546_ = v_a_6530_;
                        v___y_6547_ = v_a_6531_;
                        v___y_6548_ = v_a_6532_;
                        v___y_6549_ = v_a_6533_;
                        v___y_6550_ = v_a_6534_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___f_6541_);
                        lean_dec(v_tacticName_6525_);
                        return v___x_6555_;
                    }
                }
            }
            1 => {
                v___x_6551_ = 1;
                v___x_6552_ = l_Lean_Elab_Tactic_closeMainGoalUsing(
                    v_tacticName_6525_,
                    v___f_6541_,
                    v___x_6551_,
                    v___y_6543_,
                    v___y_6544_,
                    v___y_6545_,
                    v___y_6546_,
                    v___y_6547_,
                    v___y_6548_,
                    v___y_6549_,
                    v___y_6550_,
                );
                return v___x_6552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecideCore___boxed(
    mut v_tacticName_6556_: *mut LeanObject,
    mut v_cfg_6557_: *mut LeanObject,
    mut v_a_6558_: *mut LeanObject,
    mut v_a_6559_: *mut LeanObject,
    mut v_a_6560_: *mut LeanObject,
    mut v_a_6561_: *mut LeanObject,
    mut v_a_6562_: *mut LeanObject,
    mut v_a_6563_: *mut LeanObject,
    mut v_a_6564_: *mut LeanObject,
    mut v_a_6565_: *mut LeanObject,
    mut v_a_6566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6567_: *mut LeanObject = core::ptr::null_mut();
    v_res_6567_ = l_Lean_Elab_Tactic_evalDecideCore(
        v_tacticName_6556_,
        v_cfg_6557_,
        v_a_6558_,
        v_a_6559_,
        v_a_6560_,
        v_a_6561_,
        v_a_6562_,
        v_a_6563_,
        v_a_6564_,
        v_a_6565_,
    );
    lean_dec(v_a_6565_);
    lean_dec_ref(v_a_6564_);
    lean_dec(v_a_6563_);
    lean_dec_ref(v_a_6562_);
    lean_dec(v_a_6561_);
    lean_dec_ref(v_a_6560_);
    lean_dec(v_a_6559_);
    lean_dec_ref(v_a_6558_);
    lean_dec_ref(v_cfg_6557_);
    return v_res_6567_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    v___x_6568_ = lean_box(0);
    v___x_6569_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_6570_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6570_, 0, v___x_6569_);
    lean_ctor_set(v___x_6570_, 1, v___x_6568_);
    return v___x_6570_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_6572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut LeanObject = core::ptr::null_mut();
    v___x_6572_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___closed__0);
    v___x_6573_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6573_, 0, v___x_6572_);
    return v___x_6573_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg___boxed(
    mut v___y_6574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6575_: *mut LeanObject = core::ptr::null_mut();
    v_res_6575_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
    return v_res_6575_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(
    mut v_00_u03b1_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
    mut v___y_6580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    v___x_6582_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
    return v___x_6582_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___boxed(
    mut v_00_u03b1_6583_: *mut LeanObject,
    mut v___y_6584_: *mut LeanObject,
    mut v___y_6585_: *mut LeanObject,
    mut v___y_6586_: *mut LeanObject,
    mut v___y_6587_: *mut LeanObject,
    mut v___y_6588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6589_: *mut LeanObject = core::ptr::null_mut();
    v_res_6589_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0(v_00_u03b1_6583_, v___y_6584_, v___y_6585_, v___y_6586_, v___y_6587_);
    lean_dec(v___y_6587_);
    lean_dec_ref(v___y_6586_);
    lean_dec(v___y_6585_);
    lean_dec_ref(v___y_6584_);
    return v_res_6589_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    v___x_6592_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__1;
    v___x_6593_ = l_Lean_stringToMessageData(v___x_6592_);
    return v___x_6593_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(
    mut v_ctor_6594_: *mut LeanObject,
    mut v_args_6595_: *mut LeanObject,
    mut v___y_6596_: *mut LeanObject,
    mut v___y_6597_: *mut LeanObject,
    mut v___y_6598_: *mut LeanObject,
    mut v___y_6599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6621_: u8 = 0;
    let mut v___x_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: u8 = 0;
    let mut v___x_6624_: u8 = 0;
    let mut v___x_6625_: u8 = 0;
    let mut v___x_6626_: u8 = 0;
    let mut v___x_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6630_: u8 = 0;
    let mut v_a_6631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6634_: u8 = 0;
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6638_: u8 = 0;
    let mut v_a_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6642_: u8 = 0;
    let mut v___x_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6646_: u8 = 0;
    let mut v_a_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6650_: u8 = 0;
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6654_: u8 = 0;
    let mut v_a_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6658_: u8 = 0;
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6662_: u8 = 0;
    let mut v___x_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: u8 = 0;
    let mut v___x_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: u8 = 0;
    let mut v___x_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6674_: u8 = 0;
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6663_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__0;
                v___x_6664_ = lean_string_dec_eq(v_ctor_6594_, v___x_6663_);
                if v___x_6664_ == 0 {
                    v___x_6665_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr_spec__0___redArg();
                    return v___x_6665_;
                } else {
                    v___x_6666_ = lean_array_get_size(v_args_6595_);
                    v___x_6667_ = lean_unsigned_to_nat(4);
                    v___x_6668_ = lean_nat_dec_eq(v___x_6666_, v___x_6667_);
                    if v___x_6668_ == 0 {
                        v___x_6669_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___closed__2);
                        v___x_6670_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9_spec__14_spec__17_spec__21___redArg(v___x_6669_, v___y_6596_, v___y_6597_, v___y_6598_, v___y_6599_);
                        v_a_6671_ = lean_ctor_get(v___x_6670_, 0);
                        v_isSharedCheck_6678_ = (!lean_is_exclusive(v___x_6670_)) as u8;
                        if v_isSharedCheck_6678_ == 0 {
                            v___x_6673_ = v___x_6670_;
                            v_isShared_6674_ = v_isSharedCheck_6678_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_6671_);
                            lean_dec(v___x_6670_);
                            v___x_6673_ = lean_box(0);
                            v_isShared_6674_ = v_isSharedCheck_6678_;
                            state = 12;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6602_ = l_Lean_instInhabitedExpr;
                v___x_6603_ = lean_unsigned_to_nat(0);
                v___x_6604_ = lean_array_get_borrowed(v___x_6602_, v_args_6595_, v___x_6603_);
                lean_inc(v___x_6604_);
                v___x_6605_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                    v___x_6604_,
                    v___y_6596_,
                    v___y_6597_,
                    v___y_6598_,
                    v___y_6599_,
                );
                if lean_obj_tag(v___x_6605_) == 0 {
                    v_a_6606_ = lean_ctor_get(v___x_6605_, 0);
                    lean_inc(v_a_6606_);
                    lean_dec_ref_known(v___x_6605_, 1);
                    v___x_6607_ = lean_unsigned_to_nat(1);
                    v___x_6608_ = lean_array_get_borrowed(v___x_6602_, v_args_6595_, v___x_6607_);
                    lean_inc(v___x_6608_);
                    v___x_6609_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                        v___x_6608_,
                        v___y_6596_,
                        v___y_6597_,
                        v___y_6598_,
                        v___y_6599_,
                    );
                    if lean_obj_tag(v___x_6609_) == 0 {
                        v_a_6610_ = lean_ctor_get(v___x_6609_, 0);
                        lean_inc(v_a_6610_);
                        lean_dec_ref_known(v___x_6609_, 1);
                        v___x_6611_ = lean_unsigned_to_nat(2);
                        v___x_6612_ =
                            lean_array_get_borrowed(v___x_6602_, v_args_6595_, v___x_6611_);
                        lean_inc(v___x_6612_);
                        v___x_6613_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                            v___x_6612_,
                            v___y_6596_,
                            v___y_6597_,
                            v___y_6598_,
                            v___y_6599_,
                        );
                        if lean_obj_tag(v___x_6613_) == 0 {
                            v_a_6614_ = lean_ctor_get(v___x_6613_, 0);
                            lean_inc(v_a_6614_);
                            lean_dec_ref_known(v___x_6613_, 1);
                            v___x_6615_ = lean_unsigned_to_nat(3);
                            v___x_6616_ =
                                lean_array_get_borrowed(v___x_6602_, v_args_6595_, v___x_6615_);
                            lean_inc(v___x_6616_);
                            v___x_6617_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                v___x_6616_,
                                v___y_6596_,
                                v___y_6597_,
                                v___y_6598_,
                                v___y_6599_,
                            );
                            if lean_obj_tag(v___x_6617_) == 0 {
                                v_a_6618_ = lean_ctor_get(v___x_6617_, 0);
                                v_isSharedCheck_6630_ = (!lean_is_exclusive(v___x_6617_)) as u8;
                                if v_isSharedCheck_6630_ == 0 {
                                    v___x_6620_ = v___x_6617_;
                                    v_isShared_6621_ = v_isSharedCheck_6630_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_6618_);
                                    lean_dec(v___x_6617_);
                                    v___x_6620_ = lean_box(0);
                                    v_isShared_6621_ = v_isSharedCheck_6630_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_6614_);
                                lean_dec(v_a_6610_);
                                lean_dec(v_a_6606_);
                                v_a_6631_ = lean_ctor_get(v___x_6617_, 0);
                                v_isSharedCheck_6638_ = (!lean_is_exclusive(v___x_6617_)) as u8;
                                if v_isSharedCheck_6638_ == 0 {
                                    v___x_6633_ = v___x_6617_;
                                    v_isShared_6634_ = v_isSharedCheck_6638_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_6631_);
                                    lean_dec(v___x_6617_);
                                    v___x_6633_ = lean_box(0);
                                    v_isShared_6634_ = v_isSharedCheck_6638_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_6610_);
                            lean_dec(v_a_6606_);
                            v_a_6639_ = lean_ctor_get(v___x_6613_, 0);
                            v_isSharedCheck_6646_ = (!lean_is_exclusive(v___x_6613_)) as u8;
                            if v_isSharedCheck_6646_ == 0 {
                                v___x_6641_ = v___x_6613_;
                                v_isShared_6642_ = v_isSharedCheck_6646_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6639_);
                                lean_dec(v___x_6613_);
                                v___x_6641_ = lean_box(0);
                                v_isShared_6642_ = v_isSharedCheck_6646_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6606_);
                        v_a_6647_ = lean_ctor_get(v___x_6609_, 0);
                        v_isSharedCheck_6654_ = (!lean_is_exclusive(v___x_6609_)) as u8;
                        if v_isSharedCheck_6654_ == 0 {
                            v___x_6649_ = v___x_6609_;
                            v_isShared_6650_ = v_isSharedCheck_6654_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6647_);
                            lean_dec(v___x_6609_);
                            v___x_6649_ = lean_box(0);
                            v_isShared_6650_ = v_isSharedCheck_6654_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_6655_ = lean_ctor_get(v___x_6605_, 0);
                    v_isSharedCheck_6662_ = (!lean_is_exclusive(v___x_6605_)) as u8;
                    if v_isSharedCheck_6662_ == 0 {
                        v___x_6657_ = v___x_6605_;
                        v_isShared_6658_ = v_isSharedCheck_6662_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6655_);
                        lean_dec(v___x_6605_);
                        v___x_6657_ = lean_box(0);
                        v_isShared_6658_ = v_isSharedCheck_6662_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6622_ = lean_alloc_ctor(0, 0, (4) as u32);
                v___x_6623_ = (lean_unbox(v_a_6606_) as u8);
                lean_dec(v_a_6606_);
                lean_ctor_set_uint8(v___x_6622_, 0 as u32, v___x_6623_);
                v___x_6624_ = (lean_unbox(v_a_6610_) as u8);
                lean_dec(v_a_6610_);
                lean_ctor_set_uint8(v___x_6622_, 1 as u32, v___x_6624_);
                v___x_6625_ = (lean_unbox(v_a_6614_) as u8);
                lean_dec(v_a_6614_);
                lean_ctor_set_uint8(v___x_6622_, 2 as u32, v___x_6625_);
                v___x_6626_ = (lean_unbox(v_a_6618_) as u8);
                lean_dec(v_a_6618_);
                lean_ctor_set_uint8(v___x_6622_, 3 as u32, v___x_6626_);
                if v_isShared_6621_ == 0 {
                    lean_ctor_set(v___x_6620_, 0, v___x_6622_);
                    v___x_6628_ = v___x_6620_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6629_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6629_, 0, v___x_6622_);
                    v___x_6628_ = v_reuseFailAlloc_6629_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6628_;
            }
            4 => {
                if v_isShared_6634_ == 0 {
                    v___x_6636_ = v___x_6633_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6637_, 0, v_a_6631_);
                    v___x_6636_ = v_reuseFailAlloc_6637_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6636_;
            }
            6 => {
                if v_isShared_6642_ == 0 {
                    v___x_6644_ = v___x_6641_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6645_, 0, v_a_6639_);
                    v___x_6644_ = v_reuseFailAlloc_6645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6644_;
            }
            8 => {
                if v_isShared_6650_ == 0 {
                    v___x_6652_ = v___x_6649_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6653_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6653_, 0, v_a_6647_);
                    v___x_6652_ = v_reuseFailAlloc_6653_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6652_;
            }
            10 => {
                if v_isShared_6658_ == 0 {
                    v___x_6660_ = v___x_6657_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6661_, 0, v_a_6655_);
                    v___x_6660_ = v_reuseFailAlloc_6661_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6660_;
            }
            12 => {
                if v_isShared_6674_ == 0 {
                    v___x_6676_ = v___x_6673_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6677_, 0, v_a_6671_);
                    v___x_6676_ = v_reuseFailAlloc_6677_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0___boxed(
    mut v_ctor_6679_: *mut LeanObject,
    mut v_args_6680_: *mut LeanObject,
    mut v___y_6681_: *mut LeanObject,
    mut v___y_6682_: *mut LeanObject,
    mut v___y_6683_: *mut LeanObject,
    mut v___y_6684_: *mut LeanObject,
    mut v___y_6685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6686_: *mut LeanObject = core::ptr::null_mut();
    v_res_6686_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___lam__0(v_ctor_6679_, v_args_6680_, v___y_6681_, v___y_6682_, v___y_6683_, v___y_6684_);
    lean_dec(v___y_6684_);
    lean_dec_ref(v___y_6683_);
    lean_dec(v___y_6682_);
    lean_dec_ref(v___y_6681_);
    lean_dec_ref(v_args_6680_);
    lean_dec_ref(v_ctor_6679_);
    return v_res_6686_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(
    mut v_a_6697_: *mut LeanObject,
    mut v_a_6698_: *mut LeanObject,
    mut v_a_6699_: *mut LeanObject,
    mut v_a_6700_: *mut LeanObject,
    mut v_a_6701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    v___f_6703_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__0;
    v___x_6704_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5;
    v___x_6705_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_6704_,
        v___f_6703_,
        v_a_6697_,
        v_a_6698_,
        v_a_6699_,
        v_a_6700_,
        v_a_6701_,
    );
    return v___x_6705_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___boxed(
    mut v_a_6706_: *mut LeanObject,
    mut v_a_6707_: *mut LeanObject,
    mut v_a_6708_: *mut LeanObject,
    mut v_a_6709_: *mut LeanObject,
    mut v_a_6710_: *mut LeanObject,
    mut v_a_6711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6712_: *mut LeanObject = core::ptr::null_mut();
    v_res_6712_ =
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(
            v_a_6706_, v_a_6707_, v_a_6708_, v_a_6709_, v_a_6710_,
        );
    lean_dec(v_a_6710_);
    lean_dec_ref(v_a_6709_);
    lean_dec(v_a_6708_);
    lean_dec_ref(v_a_6707_);
    return v_res_6712_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1()
-> *mut LeanObject {
    let mut v___x_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6716_: *mut LeanObject = core::ptr::null_mut();
    v___x_6714_ = lean_box(0);
    v___x_6715_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5;
    v___x_6716_ = l_Lean_Expr_const___override(v___x_6715_, v___x_6714_);
    return v___x_6716_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2()
-> *mut LeanObject {
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6718_: *mut LeanObject = core::ptr::null_mut();
    v___x_6717_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
    v___x_6718_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6718_, 0, v___x_6717_);
    return v___x_6718_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3()
-> *mut LeanObject {
    let mut v___x_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    v___x_6719_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
    v___x_6720_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__0;
    v___x_6721_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6721_, 0, v___x_6720_);
    lean_ctor_set(v___x_6721_, 1, v___x_6719_);
    return v___x_6721_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig()
-> *mut LeanObject {
    let mut v___x_6722_: *mut LeanObject = core::ptr::null_mut();
    v___x_6722_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__3);
    return v___x_6722_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut LeanObject = core::ptr::null_mut();
    v___x_6723_ = lean_box(0);
    v___x_6724_ = l_Lean_Elab_abortTermExceptionId;
    v___x_6725_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6725_, 0, v___x_6724_);
    lean_ctor_set(v___x_6725_, 1, v___x_6723_);
    return v___x_6725_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
    v___x_6727_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___closed__0);
    v___x_6728_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6728_, 0, v___x_6727_);
    return v___x_6728_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(
    mut v___y_6729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6730_: *mut LeanObject = core::ptr::null_mut();
    v_res_6730_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
    return v_res_6730_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut LeanObject = core::ptr::null_mut();
    v___x_6732_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__0;
    v___x_6733_ = l_Lean_stringToMessageData(v___x_6732_);
    return v___x_6733_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    v___x_6734_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__1);
    v___x_6735_ = l_Lean_MessageData_ofExpr(v___x_6734_);
    return v___x_6735_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    v___x_6736_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__2);
    v___x_6737_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__1);
    v___x_6738_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6738_, 0, v___x_6737_);
    lean_ctor_set(v___x_6738_, 1, v___x_6736_);
    return v___x_6738_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut LeanObject = core::ptr::null_mut();
    v___x_6739_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecideCore_diagnose_spec__2_spec__3_spec__5_spec__9___redArg___closed__3);
    v___x_6740_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__3);
    v___x_6741_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_6741_, 0, v___x_6740_);
    lean_ctor_set(v___x_6741_, 1, v___x_6739_);
    return v___x_6741_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    v___x_6743_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__5;
    v___x_6744_ = l_Lean_stringToMessageData(v___x_6743_);
    return v___x_6744_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8()
-> *mut LeanObject {
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    v___x_6746_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__7;
    v___x_6747_ = l_Lean_stringToMessageData(v___x_6746_);
    return v___x_6747_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(
    mut v_stx_6748_: *mut LeanObject,
    mut v_a_6749_: *mut LeanObject,
    mut v_a_6750_: *mut LeanObject,
    mut v_a_6751_: *mut LeanObject,
    mut v_a_6752_: *mut LeanObject,
    mut v_a_6753_: *mut LeanObject,
    mut v_a_6754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: u8 = 0;
    let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6774_: u8 = 0;
    let mut v_cancelTk_x3f_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6776_: u8 = 0;
    let mut v_inheritedTraceOptions_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: u8 = 0;
    let mut v_ref_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6795_: u8 = 0;
    let mut v_id_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6799_: u8 = 0;
    let mut v___x_6800_: u8 = 0;
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6809_: u8 = 0;
    let mut v_unused_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6821_: u8 = 0;
    let mut v___x_6822_: u8 = 0;
    let mut v___y_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: u8 = 0;
    let mut v___x_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6839_: u8 = 0;
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6843_: u8 = 0;
    let mut v_a_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6847_: u8 = 0;
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6851_: u8 = 0;
    let mut v_a_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6855_: u8 = 0;
    let mut v___x_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6859_: u8 = 0;
    let mut v___y_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6874_: u8 = 0;
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6878_: u8 = 0;
    let mut v___x_6879_: u8 = 0;
    let mut v___x_6880_: u8 = 0;
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6885_: u8 = 0;
    let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6889_: u8 = 0;
    let mut v_a_6890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6893_: u8 = 0;
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_6756_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig___closed__2);
                v___x_6757_ = 1;
                v___x_6758_ = lean_box(0);
                v___x_6759_ = lean_box((v___x_6757_) as usize);
                v___x_6760_ = lean_box((v___x_6757_) as usize);
                lean_inc(v_stx_6748_);
                v___x_6761_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_6761_, 0, v_stx_6748_);
                lean_closure_set(v___x_6761_, 1, v_ty_x3f_6756_);
                lean_closure_set(v___x_6761_, 2, v___x_6759_);
                lean_closure_set(v___x_6761_, 3, v___x_6760_);
                lean_closure_set(v___x_6761_, 4, v___x_6758_);
                v_fileName_6762_ = lean_ctor_get(v_a_6753_, 0);
                v_fileMap_6763_ = lean_ctor_get(v_a_6753_, 1);
                v_options_6764_ = lean_ctor_get(v_a_6753_, 2);
                v_currRecDepth_6765_ = lean_ctor_get(v_a_6753_, 3);
                v_maxRecDepth_6766_ = lean_ctor_get(v_a_6753_, 4);
                v_ref_6767_ = lean_ctor_get(v_a_6753_, 5);
                v_currNamespace_6768_ = lean_ctor_get(v_a_6753_, 6);
                v_openDecls_6769_ = lean_ctor_get(v_a_6753_, 7);
                v_initHeartbeats_6770_ = lean_ctor_get(v_a_6753_, 8);
                v_maxHeartbeats_6771_ = lean_ctor_get(v_a_6753_, 9);
                v_quotContext_6772_ = lean_ctor_get(v_a_6753_, 10);
                v_currMacroScope_6773_ = lean_ctor_get(v_a_6753_, 11);
                v_diag_6774_ = lean_ctor_get_uint8(
                    v_a_6753_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6775_ = lean_ctor_get(v_a_6753_, 12);
                v_suppressElabErrors_6776_ = lean_ctor_get_uint8(
                    v_a_6753_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6777_ = lean_ctor_get(v_a_6753_, 13);
                v___x_6778_ = 1;
                v_ref_6779_ = l_Lean_replaceRef(v_stx_6748_, v_ref_6767_);
                lean_dec(v_stx_6748_);
                lean_inc_ref(v_inheritedTraceOptions_6777_);
                lean_inc(v_cancelTk_x3f_6775_);
                lean_inc(v_currMacroScope_6773_);
                lean_inc(v_quotContext_6772_);
                lean_inc(v_maxHeartbeats_6771_);
                lean_inc(v_initHeartbeats_6770_);
                lean_inc(v_openDecls_6769_);
                lean_inc(v_currNamespace_6768_);
                lean_inc(v_maxRecDepth_6766_);
                lean_inc(v_currRecDepth_6765_);
                lean_inc_ref(v_options_6764_);
                lean_inc_ref(v_fileMap_6763_);
                lean_inc_ref(v_fileName_6762_);
                v___x_6780_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_6780_, 0, v_fileName_6762_);
                lean_ctor_set(v___x_6780_, 1, v_fileMap_6763_);
                lean_ctor_set(v___x_6780_, 2, v_options_6764_);
                lean_ctor_set(v___x_6780_, 3, v_currRecDepth_6765_);
                lean_ctor_set(v___x_6780_, 4, v_maxRecDepth_6766_);
                lean_ctor_set(v___x_6780_, 5, v_ref_6779_);
                lean_ctor_set(v___x_6780_, 6, v_currNamespace_6768_);
                lean_ctor_set(v___x_6780_, 7, v_openDecls_6769_);
                lean_ctor_set(v___x_6780_, 8, v_initHeartbeats_6770_);
                lean_ctor_set(v___x_6780_, 9, v_maxHeartbeats_6771_);
                lean_ctor_set(v___x_6780_, 10, v_quotContext_6772_);
                lean_ctor_set(v___x_6780_, 11, v_currMacroScope_6773_);
                lean_ctor_set(v___x_6780_, 12, v_cancelTk_x3f_6775_);
                lean_ctor_set(v___x_6780_, 13, v_inheritedTraceOptions_6777_);
                lean_ctor_set_uint8(
                    v___x_6780_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_6774_,
                );
                lean_ctor_set_uint8(
                    v___x_6780_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6776_,
                );
                v___x_6781_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_6761_,
                        v___x_6778_,
                        v_a_6749_,
                        v_a_6750_,
                        v_a_6751_,
                        v_a_6752_,
                        v___x_6780_,
                        v_a_6754_,
                    );
                if lean_obj_tag(v___x_6781_) == 0 {
                    v_a_6782_ = lean_ctor_get(v___x_6781_, 0);
                    lean_inc(v_a_6782_);
                    lean_dec_ref_known(v___x_6781_, 1);
                    v___x_6783_ = l_Lean_instantiateMVars___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__1___redArg(v_a_6782_, v_a_6752_);
                    v_a_6784_ = lean_ctor_get(v___x_6783_, 0);
                    lean_inc(v_a_6784_);
                    lean_dec_ref(v___x_6783_);
                    v___x_6879_ = l_Lean_Expr_hasSorry(v_a_6784_);
                    if v___x_6879_ == 0 {
                        v___y_6824_ = v_a_6749_;
                        v___y_6825_ = v_a_6750_;
                        v___y_6826_ = v_a_6751_;
                        v___y_6827_ = v_a_6752_;
                        v___y_6828_ = v___x_6780_;
                        v___y_6829_ = v_a_6754_;
                        state = 5;
                        continue;
                    } else {
                        v___x_6880_ = l_Lean_Expr_hasSyntheticSorry(v_a_6784_);
                        if v___x_6880_ == 0 {
                            v___y_6861_ = v_a_6749_;
                            v___y_6862_ = v_a_6750_;
                            v___y_6863_ = v_a_6751_;
                            v___y_6864_ = v_a_6752_;
                            v___y_6865_ = v___x_6780_;
                            v___y_6866_ = v_a_6754_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_6784_);
                            lean_dec_ref_known(v___x_6780_, 14);
                            v___x_6881_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
                            v_a_6882_ = lean_ctor_get(v___x_6881_, 0);
                            v_isSharedCheck_6889_ = (!lean_is_exclusive(v___x_6881_)) as u8;
                            if v_isSharedCheck_6889_ == 0 {
                                v___x_6884_ = v___x_6881_;
                                v_isShared_6885_ = v_isSharedCheck_6889_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_6882_);
                                lean_dec(v___x_6881_);
                                v___x_6884_ = lean_box(0);
                                v_isShared_6885_ = v_isSharedCheck_6889_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_6780_, 14);
                    v_a_6890_ = lean_ctor_get(v___x_6781_, 0);
                    v_isSharedCheck_6897_ = (!lean_is_exclusive(v___x_6781_)) as u8;
                    if v_isSharedCheck_6897_ == 0 {
                        v___x_6892_ = v___x_6781_;
                        v_isShared_6893_ = v_isSharedCheck_6897_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_6890_);
                        lean_dec(v___x_6781_);
                        v___x_6892_ = lean_box(0);
                        v_isShared_6893_ = v_isSharedCheck_6897_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_6795_ == 0 {
                    if lean_obj_tag(v___y_6789_) == 0 {
                        lean_dec_ref_known(v___y_6789_, 2);
                        lean_dec_ref(v___y_6788_);
                        lean_dec(v_a_6784_);
                        return v___y_6791_;
                    } else {
                        v_id_6796_ = lean_ctor_get(v___y_6789_, 0);
                        v_isSharedCheck_6809_ = (!lean_is_exclusive(v___y_6789_)) as u8;
                        if v_isSharedCheck_6809_ == 0 {
                            v_unused_6810_ = lean_ctor_get(v___y_6789_, 1);
                            lean_dec(v_unused_6810_);
                            v___x_6798_ = v___y_6789_;
                            v_isShared_6799_ = v_isSharedCheck_6809_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_6796_);
                            lean_dec(v___y_6789_);
                            v___x_6798_ = lean_box(0);
                            v_isShared_6799_ = v_isSharedCheck_6809_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6789_);
                    lean_dec_ref(v___y_6788_);
                    lean_dec(v_a_6784_);
                    return v___y_6791_;
                }
            }
            2 => {
                v___x_6800_ = l_Lean_instBEqInternalExceptionId_beq(v___y_6790_, v_id_6796_);
                lean_dec(v_id_6796_);
                if v___x_6800_ == 0 {
                    lean_del_object(v___x_6798_);
                    lean_dec_ref(v___y_6788_);
                    lean_dec(v_a_6784_);
                    return v___y_6791_;
                } else {
                    lean_dec_ref(v___y_6791_);
                    v___x_6801_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__4);
                    v___x_6802_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__6);
                    v___x_6803_ = l_Lean_indentExpr(v_a_6784_);
                    if v_isShared_6799_ == 0 {
                        lean_ctor_set_tag(v___x_6798_, 7);
                        lean_ctor_set(v___x_6798_, 1, v___x_6803_);
                        lean_ctor_set(v___x_6798_, 0, v___x_6802_);
                        v___x_6805_ = v___x_6798_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6808_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6808_, 0, v___x_6802_);
                        lean_ctor_set(v_reuseFailAlloc_6808_, 1, v___x_6803_);
                        v___x_6805_ = v_reuseFailAlloc_6808_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6806_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6806_, 0, v___x_6805_);
                lean_ctor_set(v___x_6806_, 1, v___x_6801_);
                v___x_6807_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_6806_, v___y_6793_, v___y_6794_, v___y_6787_, v___y_6792_, v___y_6788_, v___y_6786_);
                lean_dec_ref(v___y_6788_);
                return v___x_6807_;
            }
            4 => {
                lean_inc(v_a_6784_);
                v___x_6818_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr(v_a_6784_, v___y_6814_, v___y_6815_, v___y_6816_, v___y_6817_);
                if lean_obj_tag(v___x_6818_) == 0 {
                    lean_dec_ref(v___y_6816_);
                    lean_dec(v_a_6784_);
                    return v___x_6818_;
                } else {
                    v_a_6819_ = lean_ctor_get(v___x_6818_, 0);
                    lean_inc(v_a_6819_);
                    v___x_6820_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_6821_ = l_Lean_Exception_isInterrupt(v_a_6819_);
                    if v___x_6821_ == 0 {
                        lean_inc(v_a_6819_);
                        v___x_6822_ = l_Lean_Exception_isRuntime(v_a_6819_);
                        v___y_6786_ = v___y_6817_;
                        v___y_6787_ = v___y_6814_;
                        v___y_6788_ = v___y_6816_;
                        v___y_6789_ = v_a_6819_;
                        v___y_6790_ = v___x_6820_;
                        v___y_6791_ = v___x_6818_;
                        v___y_6792_ = v___y_6815_;
                        v___y_6793_ = v___y_6812_;
                        v___y_6794_ = v___y_6813_;
                        v___y_6795_ = v___x_6822_;
                        state = 1;
                        continue;
                    } else {
                        v___y_6786_ = v___y_6817_;
                        v___y_6787_ = v___y_6814_;
                        v___y_6788_ = v___y_6816_;
                        v___y_6789_ = v_a_6819_;
                        v___y_6790_ = v___x_6820_;
                        v___y_6791_ = v___x_6818_;
                        v___y_6792_ = v___y_6815_;
                        v___y_6793_ = v___y_6812_;
                        v___y_6794_ = v___y_6813_;
                        v___y_6795_ = v___x_6821_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_6784_);
                v___x_6830_ = l_Lean_Meta_getMVars(
                    v_a_6784_,
                    v___y_6826_,
                    v___y_6827_,
                    v___y_6828_,
                    v___y_6829_,
                );
                if lean_obj_tag(v___x_6830_) == 0 {
                    v_a_6831_ = lean_ctor_get(v___x_6830_, 0);
                    lean_inc(v_a_6831_);
                    lean_dec_ref_known(v___x_6830_, 1);
                    v___x_6832_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_6831_,
                        v___x_6758_,
                        v___y_6824_,
                        v___y_6825_,
                        v___y_6826_,
                        v___y_6827_,
                        v___y_6828_,
                        v___y_6829_,
                    );
                    lean_dec(v_a_6831_);
                    if lean_obj_tag(v___x_6832_) == 0 {
                        v_a_6833_ = lean_ctor_get(v___x_6832_, 0);
                        lean_inc(v_a_6833_);
                        lean_dec_ref_known(v___x_6832_, 1);
                        v___x_6834_ = (lean_unbox(v_a_6833_) as u8);
                        lean_dec(v_a_6833_);
                        if v___x_6834_ == 0 {
                            v___y_6812_ = v___y_6824_;
                            v___y_6813_ = v___y_6825_;
                            v___y_6814_ = v___y_6826_;
                            v___y_6815_ = v___y_6827_;
                            v___y_6816_ = v___y_6828_;
                            v___y_6817_ = v___y_6829_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_6828_);
                            lean_dec(v_a_6784_);
                            v___x_6835_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
                            v_a_6836_ = lean_ctor_get(v___x_6835_, 0);
                            v_isSharedCheck_6843_ = (!lean_is_exclusive(v___x_6835_)) as u8;
                            if v_isSharedCheck_6843_ == 0 {
                                v___x_6838_ = v___x_6835_;
                                v_isShared_6839_ = v_isSharedCheck_6843_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_6836_);
                                lean_dec(v___x_6835_);
                                v___x_6838_ = lean_box(0);
                                v_isShared_6839_ = v_isSharedCheck_6843_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_6828_);
                        lean_dec(v_a_6784_);
                        v_a_6844_ = lean_ctor_get(v___x_6832_, 0);
                        v_isSharedCheck_6851_ = (!lean_is_exclusive(v___x_6832_)) as u8;
                        if v_isSharedCheck_6851_ == 0 {
                            v___x_6846_ = v___x_6832_;
                            v_isShared_6847_ = v_isSharedCheck_6851_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6844_);
                            lean_dec(v___x_6832_);
                            v___x_6846_ = lean_box(0);
                            v_isShared_6847_ = v_isSharedCheck_6851_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6828_);
                    lean_dec(v_a_6784_);
                    v_a_6852_ = lean_ctor_get(v___x_6830_, 0);
                    v_isSharedCheck_6859_ = (!lean_is_exclusive(v___x_6830_)) as u8;
                    if v_isSharedCheck_6859_ == 0 {
                        v___x_6854_ = v___x_6830_;
                        v_isShared_6855_ = v_isSharedCheck_6859_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6852_);
                        lean_dec(v___x_6830_);
                        v___x_6854_ = lean_box(0);
                        v_isShared_6855_ = v_isSharedCheck_6859_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_6839_ == 0 {
                    v___x_6841_ = v___x_6838_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6842_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6842_, 0, v_a_6836_);
                    v___x_6841_ = v_reuseFailAlloc_6842_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6841_;
            }
            8 => {
                if v_isShared_6847_ == 0 {
                    v___x_6849_ = v___x_6846_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6850_, 0, v_a_6844_);
                    v___x_6849_ = v_reuseFailAlloc_6850_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6849_;
            }
            10 => {
                if v_isShared_6855_ == 0 {
                    v___x_6857_ = v___x_6854_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6858_, 0, v_a_6852_);
                    v___x_6857_ = v_reuseFailAlloc_6858_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6857_;
            }
            12 => {
                v___x_6867_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___closed__8);
                v___x_6868_ = l_Lean_indentExpr(v_a_6784_);
                v___x_6869_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6869_, 0, v___x_6867_);
                lean_ctor_set(v___x_6869_, 1, v___x_6868_);
                v___x_6870_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_preprocessPropToDecide_spec__0___redArg(v___x_6869_, v___y_6861_, v___y_6862_, v___y_6863_, v___y_6864_, v___y_6865_, v___y_6866_);
                lean_dec_ref(v___y_6865_);
                v_a_6871_ = lean_ctor_get(v___x_6870_, 0);
                v_isSharedCheck_6878_ = (!lean_is_exclusive(v___x_6870_)) as u8;
                if v_isSharedCheck_6878_ == 0 {
                    v___x_6873_ = v___x_6870_;
                    v_isShared_6874_ = v_isSharedCheck_6878_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_6871_);
                    lean_dec(v___x_6870_);
                    v___x_6873_ = lean_box(0);
                    v_isShared_6874_ = v_isSharedCheck_6878_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_6874_ == 0 {
                    v___x_6876_ = v___x_6873_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6877_, 0, v_a_6871_);
                    v___x_6876_ = v_reuseFailAlloc_6877_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6876_;
            }
            15 => {
                if v_isShared_6885_ == 0 {
                    v___x_6887_ = v___x_6884_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6888_, 0, v_a_6882_);
                    v___x_6887_ = v_reuseFailAlloc_6888_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6887_;
            }
            17 => {
                if v_isShared_6893_ == 0 {
                    v___x_6895_ = v___x_6892_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6896_, 0, v_a_6890_);
                    v___x_6895_ = v_reuseFailAlloc_6896_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0___boxed(
    mut v_stx_6898_: *mut LeanObject,
    mut v_a_6899_: *mut LeanObject,
    mut v_a_6900_: *mut LeanObject,
    mut v_a_6901_: *mut LeanObject,
    mut v_a_6902_: *mut LeanObject,
    mut v_a_6903_: *mut LeanObject,
    mut v_a_6904_: *mut LeanObject,
    mut v_a_6905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6906_: *mut LeanObject = core::ptr::null_mut();
    v_res_6906_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_stx_6898_, v_a_6899_, v_a_6900_, v_a_6901_, v_a_6902_, v_a_6903_, v_a_6904_);
    lean_dec(v_a_6904_);
    lean_dec_ref(v_a_6903_);
    lean_dec(v_a_6902_);
    lean_dec_ref(v_a_6901_);
    lean_dec(v_a_6900_);
    lean_dec_ref(v_a_6899_);
    return v_res_6906_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(
    mut v_config_6938_: *mut LeanObject,
    mut v_item_6939_: *mut LeanObject,
    mut v___y_6940_: *mut LeanObject,
    mut v___y_6941_: *mut LeanObject,
    mut v___y_6942_: *mut LeanObject,
    mut v___y_6943_: *mut LeanObject,
    mut v___y_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_item_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: u8 = 0;
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: u8 = 0;
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: u8 = 0;
    let mut v___x_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6967_: u8 = 0;
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: u8 = 0;
    let mut v___x_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: u8 = 0;
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: u8 = 0;
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6979_: u8 = 0;
    let mut v_kernel_6980_: u8 = 0;
    let mut v_native_6981_: u8 = 0;
    let mut v_revert_6982_: u8 = 0;
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6985_: u8 = 0;
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: u8 = 0;
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6993_: u8 = 0;
    let mut v_isSharedCheck_6994_: u8 = 0;
    let mut v_a_6995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6998_: u8 = 0;
    let mut v___x_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7002_: u8 = 0;
    let mut v_a_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7006_: u8 = 0;
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7010_: u8 = 0;
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: u8 = 0;
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7018_: u8 = 0;
    let mut v_kernel_7019_: u8 = 0;
    let mut v_native_7020_: u8 = 0;
    let mut v_zetaReduce_7021_: u8 = 0;
    let mut v___x_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7024_: u8 = 0;
    let mut v___x_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: u8 = 0;
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7032_: u8 = 0;
    let mut v_isSharedCheck_7033_: u8 = 0;
    let mut v_a_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7037_: u8 = 0;
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7041_: u8 = 0;
    let mut v_a_7042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7045_: u8 = 0;
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7049_: u8 = 0;
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: u8 = 0;
    let mut v___x_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7057_: u8 = 0;
    let mut v_kernel_7058_: u8 = 0;
    let mut v_zetaReduce_7059_: u8 = 0;
    let mut v_revert_7060_: u8 = 0;
    let mut v___x_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7063_: u8 = 0;
    let mut v___x_7065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: u8 = 0;
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7071_: u8 = 0;
    let mut v_isSharedCheck_7072_: u8 = 0;
    let mut v_a_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7076_: u8 = 0;
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7080_: u8 = 0;
    let mut v_a_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7084_: u8 = 0;
    let mut v___x_7086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7088_: u8 = 0;
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: u8 = 0;
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7096_: u8 = 0;
    let mut v_native_7097_: u8 = 0;
    let mut v_zetaReduce_7098_: u8 = 0;
    let mut v_revert_7099_: u8 = 0;
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7102_: u8 = 0;
    let mut v___x_7104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: u8 = 0;
    let mut v___x_7107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7110_: u8 = 0;
    let mut v_isSharedCheck_7111_: u8 = 0;
    let mut v_a_7112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7115_: u8 = 0;
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7119_: u8 = 0;
    let mut v_a_7120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7123_: u8 = 0;
    let mut v___x_7125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7127_: u8 = 0;
    let mut v___x_7128_: u8 = 0;
    let mut v_value_7129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7134_: u8 = 0;
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6957_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5;
                v___x_6958_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
                    v_item_6939_,
                    v___x_6957_,
                    v___y_6940_,
                    v___y_6941_,
                    v___y_6942_,
                    v___y_6943_,
                    v___y_6944_,
                    v___y_6945_,
                );
                if lean_obj_tag(v___x_6958_) == 0 {
                    lean_dec_ref_known(v___x_6958_, 1);
                    v___x_6959_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_6939_);
                    if v___x_6959_ == 0 {
                        v___x_6960_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_6939_);
                        lean_inc_ref(v_item_6939_);
                        v___x_6961_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_6939_);
                        v___x_6962_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__1;
                        v___x_6963_ = lean_string_dec_eq(v___x_6960_, v___x_6962_);
                        if v___x_6963_ == 0 {
                            v___x_6964_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__2;
                            v___x_6965_ = lean_string_dec_eq(v___x_6960_, v___x_6964_);
                            if v___x_6965_ == 0 {
                                v___x_6966_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__3;
                                v___x_6967_ = lean_string_dec_eq(v___x_6960_, v___x_6966_);
                                if v___x_6967_ == 0 {
                                    v___x_6968_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__4;
                                    v___x_6969_ = lean_string_dec_eq(v___x_6960_, v___x_6968_);
                                    if v___x_6969_ == 0 {
                                        v___x_6970_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__5;
                                        v___x_6971_ = lean_string_dec_eq(v___x_6960_, v___x_6970_);
                                        lean_dec_ref(v___x_6960_);
                                        if v___x_6971_ == 0 {
                                            lean_dec_ref(v_item_6939_);
                                            lean_dec_ref(v_config_6938_);
                                            v_item_6948_ = v___x_6961_;
                                            v___y_6949_ = v___y_6940_;
                                            v___y_6950_ = v___y_6941_;
                                            v___y_6951_ = v___y_6942_;
                                            v___y_6952_ = v___y_6943_;
                                            v___y_6953_ = v___y_6944_;
                                            v___y_6954_ = v___y_6945_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_6972_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__6;
                                            v___x_6973_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_6939_,
                                                    v___x_6972_,
                                                    v___y_6940_,
                                                    v___y_6941_,
                                                    v___y_6942_,
                                                    v___y_6943_,
                                                    v___y_6944_,
                                                    v___y_6945_,
                                                );
                                            if lean_obj_tag(v___x_6973_) == 0 {
                                                lean_dec_ref_known(v___x_6973_, 1);
                                                v___x_6974_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_6961_,
                                                    );
                                                if v___x_6974_ == 0 {
                                                    lean_dec_ref(v_item_6939_);
                                                    lean_dec_ref(v_config_6938_);
                                                    v_item_6948_ = v___x_6961_;
                                                    v___y_6949_ = v___y_6940_;
                                                    v___y_6950_ = v___y_6941_;
                                                    v___y_6951_ = v___y_6942_;
                                                    v___y_6952_ = v___y_6943_;
                                                    v___y_6953_ = v___y_6944_;
                                                    v___y_6954_ = v___y_6945_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec_ref(v___x_6961_);
                                                    v___x_6975_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_6939_,
                                                            v___y_6940_,
                                                            v___y_6941_,
                                                            v___y_6942_,
                                                            v___y_6943_,
                                                            v___y_6944_,
                                                            v___y_6945_,
                                                        );
                                                    if lean_obj_tag(v___x_6975_) == 0 {
                                                        v_a_6976_ = lean_ctor_get(v___x_6975_, 0);
                                                        v_isSharedCheck_6994_ =
                                                            (!lean_is_exclusive(v___x_6975_)) as u8;
                                                        if v_isSharedCheck_6994_ == 0 {
                                                            v___x_6978_ = v___x_6975_;
                                                            v_isShared_6979_ =
                                                                v_isSharedCheck_6994_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6976_);
                                                            lean_dec(v___x_6975_);
                                                            v___x_6978_ = lean_box(0);
                                                            v_isShared_6979_ =
                                                                v_isSharedCheck_6994_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_6938_);
                                                        v_a_6995_ = lean_ctor_get(v___x_6975_, 0);
                                                        v_isSharedCheck_7002_ =
                                                            (!lean_is_exclusive(v___x_6975_)) as u8;
                                                        if v_isSharedCheck_7002_ == 0 {
                                                            v___x_6997_ = v___x_6975_;
                                                            v_isShared_6998_ =
                                                                v_isSharedCheck_7002_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_6995_);
                                                            lean_dec(v___x_6975_);
                                                            v___x_6997_ = lean_box(0);
                                                            v_isShared_6998_ =
                                                                v_isSharedCheck_7002_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_6961_);
                                                lean_dec_ref(v_item_6939_);
                                                lean_dec_ref(v_config_6938_);
                                                v_a_7003_ = lean_ctor_get(v___x_6973_, 0);
                                                v_isSharedCheck_7010_ =
                                                    (!lean_is_exclusive(v___x_6973_)) as u8;
                                                if v_isSharedCheck_7010_ == 0 {
                                                    v___x_7005_ = v___x_6973_;
                                                    v_isShared_7006_ = v_isSharedCheck_7010_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7003_);
                                                    lean_dec(v___x_6973_);
                                                    v___x_7005_ = lean_box(0);
                                                    v_isShared_7006_ = v_isSharedCheck_7010_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6960_);
                                        v___x_7011_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__7;
                                        v___x_7012_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_6939_,
                                                v___x_7011_,
                                                v___y_6940_,
                                                v___y_6941_,
                                                v___y_6942_,
                                                v___y_6943_,
                                                v___y_6944_,
                                                v___y_6945_,
                                            );
                                        if lean_obj_tag(v___x_7012_) == 0 {
                                            lean_dec_ref_known(v___x_7012_, 1);
                                            v___x_7013_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_6961_,
                                                );
                                            if v___x_7013_ == 0 {
                                                lean_dec_ref(v_item_6939_);
                                                lean_dec_ref(v_config_6938_);
                                                v_item_6948_ = v___x_6961_;
                                                v___y_6949_ = v___y_6940_;
                                                v___y_6950_ = v___y_6941_;
                                                v___y_6951_ = v___y_6942_;
                                                v___y_6952_ = v___y_6943_;
                                                v___y_6953_ = v___y_6944_;
                                                v___y_6954_ = v___y_6945_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_dec_ref(v___x_6961_);
                                                v___x_7014_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_6939_,
                                                    v___y_6940_,
                                                    v___y_6941_,
                                                    v___y_6942_,
                                                    v___y_6943_,
                                                    v___y_6944_,
                                                    v___y_6945_,
                                                );
                                                if lean_obj_tag(v___x_7014_) == 0 {
                                                    v_a_7015_ = lean_ctor_get(v___x_7014_, 0);
                                                    v_isSharedCheck_7033_ =
                                                        (!lean_is_exclusive(v___x_7014_)) as u8;
                                                    if v_isSharedCheck_7033_ == 0 {
                                                        v___x_7017_ = v___x_7014_;
                                                        v_isShared_7018_ = v_isSharedCheck_7033_;
                                                        state = 10;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7015_);
                                                        lean_dec(v___x_7014_);
                                                        v___x_7017_ = lean_box(0);
                                                        v_isShared_7018_ = v_isSharedCheck_7033_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_6938_);
                                                    v_a_7034_ = lean_ctor_get(v___x_7014_, 0);
                                                    v_isSharedCheck_7041_ =
                                                        (!lean_is_exclusive(v___x_7014_)) as u8;
                                                    if v_isSharedCheck_7041_ == 0 {
                                                        v___x_7036_ = v___x_7014_;
                                                        v_isShared_7037_ = v_isSharedCheck_7041_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_7034_);
                                                        lean_dec(v___x_7014_);
                                                        v___x_7036_ = lean_box(0);
                                                        v_isShared_7037_ = v_isSharedCheck_7041_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_6961_);
                                            lean_dec_ref(v_item_6939_);
                                            lean_dec_ref(v_config_6938_);
                                            v_a_7042_ = lean_ctor_get(v___x_7012_, 0);
                                            v_isSharedCheck_7049_ =
                                                (!lean_is_exclusive(v___x_7012_)) as u8;
                                            if v_isSharedCheck_7049_ == 0 {
                                                v___x_7044_ = v___x_7012_;
                                                v_isShared_7045_ = v_isSharedCheck_7049_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7042_);
                                                lean_dec(v___x_7012_);
                                                v___x_7044_ = lean_box(0);
                                                v_isShared_7045_ = v_isSharedCheck_7049_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_6960_);
                                    v___x_7050_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__8;
                                    v___x_7051_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_6939_,
                                        v___x_7050_,
                                        v___y_6940_,
                                        v___y_6941_,
                                        v___y_6942_,
                                        v___y_6943_,
                                        v___y_6944_,
                                        v___y_6945_,
                                    );
                                    if lean_obj_tag(v___x_7051_) == 0 {
                                        lean_dec_ref_known(v___x_7051_, 1);
                                        v___x_7052_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_6961_,
                                        );
                                        if v___x_7052_ == 0 {
                                            lean_dec_ref(v_item_6939_);
                                            lean_dec_ref(v_config_6938_);
                                            v_item_6948_ = v___x_6961_;
                                            v___y_6949_ = v___y_6940_;
                                            v___y_6950_ = v___y_6941_;
                                            v___y_6951_ = v___y_6942_;
                                            v___y_6952_ = v___y_6943_;
                                            v___y_6953_ = v___y_6944_;
                                            v___y_6954_ = v___y_6945_;
                                            state = 1;
                                            continue;
                                        } else {
                                            lean_dec_ref(v___x_6961_);
                                            v___x_7053_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_6939_,
                                                v___y_6940_,
                                                v___y_6941_,
                                                v___y_6942_,
                                                v___y_6943_,
                                                v___y_6944_,
                                                v___y_6945_,
                                            );
                                            if lean_obj_tag(v___x_7053_) == 0 {
                                                v_a_7054_ = lean_ctor_get(v___x_7053_, 0);
                                                v_isSharedCheck_7072_ =
                                                    (!lean_is_exclusive(v___x_7053_)) as u8;
                                                if v_isSharedCheck_7072_ == 0 {
                                                    v___x_7056_ = v___x_7053_;
                                                    v_isShared_7057_ = v_isSharedCheck_7072_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7054_);
                                                    lean_dec(v___x_7053_);
                                                    v___x_7056_ = lean_box(0);
                                                    v_isShared_7057_ = v_isSharedCheck_7072_;
                                                    state = 18;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_6938_);
                                                v_a_7073_ = lean_ctor_get(v___x_7053_, 0);
                                                v_isSharedCheck_7080_ =
                                                    (!lean_is_exclusive(v___x_7053_)) as u8;
                                                if v_isSharedCheck_7080_ == 0 {
                                                    v___x_7075_ = v___x_7053_;
                                                    v_isShared_7076_ = v_isSharedCheck_7080_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_7073_);
                                                    lean_dec(v___x_7053_);
                                                    v___x_7075_ = lean_box(0);
                                                    v_isShared_7076_ = v_isSharedCheck_7080_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_6961_);
                                        lean_dec_ref(v_item_6939_);
                                        lean_dec_ref(v_config_6938_);
                                        v_a_7081_ = lean_ctor_get(v___x_7051_, 0);
                                        v_isSharedCheck_7088_ =
                                            (!lean_is_exclusive(v___x_7051_)) as u8;
                                        if v_isSharedCheck_7088_ == 0 {
                                            v___x_7083_ = v___x_7051_;
                                            v_isShared_7084_ = v_isSharedCheck_7088_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_inc(v_a_7081_);
                                            lean_dec(v___x_7051_);
                                            v___x_7083_ = lean_box(0);
                                            v_isShared_7084_ = v_isSharedCheck_7088_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_6960_);
                                v___x_7089_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__9;
                                v___x_7090_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                    v_item_6939_,
                                    v___x_7089_,
                                    v___y_6940_,
                                    v___y_6941_,
                                    v___y_6942_,
                                    v___y_6943_,
                                    v___y_6944_,
                                    v___y_6945_,
                                );
                                if lean_obj_tag(v___x_7090_) == 0 {
                                    lean_dec_ref_known(v___x_7090_, 1);
                                    v___x_7091_ =
                                        l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_6961_);
                                    if v___x_7091_ == 0 {
                                        lean_dec_ref(v_item_6939_);
                                        lean_dec_ref(v_config_6938_);
                                        v_item_6948_ = v___x_6961_;
                                        v___y_6949_ = v___y_6940_;
                                        v___y_6950_ = v___y_6941_;
                                        v___y_6951_ = v___y_6942_;
                                        v___y_6952_ = v___y_6943_;
                                        v___y_6953_ = v___y_6944_;
                                        v___y_6954_ = v___y_6945_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___x_6961_);
                                        v___x_7092_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                            v_item_6939_,
                                            v___y_6940_,
                                            v___y_6941_,
                                            v___y_6942_,
                                            v___y_6943_,
                                            v___y_6944_,
                                            v___y_6945_,
                                        );
                                        if lean_obj_tag(v___x_7092_) == 0 {
                                            v_a_7093_ = lean_ctor_get(v___x_7092_, 0);
                                            v_isSharedCheck_7111_ =
                                                (!lean_is_exclusive(v___x_7092_)) as u8;
                                            if v_isSharedCheck_7111_ == 0 {
                                                v___x_7095_ = v___x_7092_;
                                                v_isShared_7096_ = v_isSharedCheck_7111_;
                                                state = 26;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7093_);
                                                lean_dec(v___x_7092_);
                                                v___x_7095_ = lean_box(0);
                                                v_isShared_7096_ = v_isSharedCheck_7111_;
                                                state = 26;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v_config_6938_);
                                            v_a_7112_ = lean_ctor_get(v___x_7092_, 0);
                                            v_isSharedCheck_7119_ =
                                                (!lean_is_exclusive(v___x_7092_)) as u8;
                                            if v_isSharedCheck_7119_ == 0 {
                                                v___x_7114_ = v___x_7092_;
                                                v_isShared_7115_ = v_isSharedCheck_7119_;
                                                state = 30;
                                                continue;
                                            } else {
                                                lean_inc(v_a_7112_);
                                                lean_dec(v___x_7092_);
                                                v___x_7114_ = lean_box(0);
                                                v_isShared_7115_ = v_isSharedCheck_7119_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_6961_);
                                    lean_dec_ref(v_item_6939_);
                                    lean_dec_ref(v_config_6938_);
                                    v_a_7120_ = lean_ctor_get(v___x_7090_, 0);
                                    v_isSharedCheck_7127_ = (!lean_is_exclusive(v___x_7090_)) as u8;
                                    if v_isSharedCheck_7127_ == 0 {
                                        v___x_7122_ = v___x_7090_;
                                        v_isShared_7123_ = v_isSharedCheck_7127_;
                                        state = 32;
                                        continue;
                                    } else {
                                        lean_inc(v_a_7120_);
                                        lean_dec(v___x_7090_);
                                        v___x_7122_ = lean_box(0);
                                        v_isShared_7123_ = v_isSharedCheck_7127_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_6960_);
                            lean_dec_ref(v_config_6938_);
                            v___x_7128_ =
                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_6961_);
                            if v___x_7128_ == 0 {
                                lean_dec_ref(v_item_6939_);
                                v_item_6948_ = v___x_6961_;
                                v___y_6949_ = v___y_6940_;
                                v___y_6950_ = v___y_6941_;
                                v___y_6951_ = v___y_6942_;
                                v___y_6952_ = v___y_6943_;
                                v___y_6953_ = v___y_6944_;
                                v___y_6954_ = v___y_6945_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v___x_6961_);
                                v_value_7129_ = lean_ctor_get(v_item_6939_, 2);
                                lean_inc(v_value_7129_);
                                lean_dec_ref(v_item_6939_);
                                v___x_7130_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0(v_value_7129_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_);
                                return v___x_7130_;
                            }
                        }
                    } else {
                        lean_dec_ref(v_config_6938_);
                        v_item_6948_ = v_item_6939_;
                        v___y_6949_ = v___y_6940_;
                        v___y_6950_ = v___y_6941_;
                        v___y_6951_ = v___y_6942_;
                        v___y_6952_ = v___y_6943_;
                        v___y_6953_ = v___y_6944_;
                        v___y_6954_ = v___y_6945_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_item_6939_);
                    lean_dec_ref(v_config_6938_);
                    v_a_7131_ = lean_ctor_get(v___x_6958_, 0);
                    v_isSharedCheck_7138_ = (!lean_is_exclusive(v___x_6958_)) as u8;
                    if v_isSharedCheck_7138_ == 0 {
                        v___x_7133_ = v___x_6958_;
                        v_isShared_7134_ = v_isSharedCheck_7138_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_a_7131_);
                        lean_dec(v___x_6958_);
                        v___x_7133_ = lean_box(0);
                        v_isShared_7134_ = v_isSharedCheck_7138_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6955_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___closed__0;
                v___x_6956_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
                    v_item_6948_,
                    v___x_6955_,
                    v___y_6949_,
                    v___y_6950_,
                    v___y_6951_,
                    v___y_6952_,
                    v___y_6953_,
                    v___y_6954_,
                );
                return v___x_6956_;
            }
            2 => {
                v_kernel_6980_ = lean_ctor_get_uint8(v_config_6938_, 0 as u32);
                v_native_6981_ = lean_ctor_get_uint8(v_config_6938_, 1 as u32);
                v_revert_6982_ = lean_ctor_get_uint8(v_config_6938_, 3 as u32);
                v_isSharedCheck_6993_ = (!lean_is_exclusive(v_config_6938_)) as u8;
                if v_isSharedCheck_6993_ == 0 {
                    v___x_6984_ = v_config_6938_;
                    v_isShared_6985_ = v_isSharedCheck_6993_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_config_6938_);
                    v___x_6984_ = lean_box(0);
                    v_isShared_6985_ = v_isSharedCheck_6993_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6985_ == 0 {
                    v___x_6987_ = v___x_6984_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6992_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6992_, 0 as u32, v_kernel_6980_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_6992_, 1 as u32, v_native_6981_);
                    v___x_6987_ = v_reuseFailAlloc_6992_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6988_ = (lean_unbox(v_a_6976_) as u8);
                lean_dec(v_a_6976_);
                lean_ctor_set_uint8(v___x_6987_, 2 as u32, v___x_6988_);
                lean_ctor_set_uint8(v___x_6987_, 3 as u32, v_revert_6982_);
                if v_isShared_6979_ == 0 {
                    lean_ctor_set(v___x_6978_, 0, v___x_6987_);
                    v___x_6990_ = v___x_6978_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6991_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6991_, 0, v___x_6987_);
                    v___x_6990_ = v_reuseFailAlloc_6991_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6990_;
            }
            6 => {
                if v_isShared_6998_ == 0 {
                    v___x_7000_ = v___x_6997_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7001_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7001_, 0, v_a_6995_);
                    v___x_7000_ = v_reuseFailAlloc_7001_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7000_;
            }
            8 => {
                if v_isShared_7006_ == 0 {
                    v___x_7008_ = v___x_7005_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7009_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7009_, 0, v_a_7003_);
                    v___x_7008_ = v_reuseFailAlloc_7009_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7008_;
            }
            10 => {
                v_kernel_7019_ = lean_ctor_get_uint8(v_config_6938_, 0 as u32);
                v_native_7020_ = lean_ctor_get_uint8(v_config_6938_, 1 as u32);
                v_zetaReduce_7021_ = lean_ctor_get_uint8(v_config_6938_, 2 as u32);
                v_isSharedCheck_7032_ = (!lean_is_exclusive(v_config_6938_)) as u8;
                if v_isSharedCheck_7032_ == 0 {
                    v___x_7023_ = v_config_6938_;
                    v_isShared_7024_ = v_isSharedCheck_7032_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_config_6938_);
                    v___x_7023_ = lean_box(0);
                    v_isShared_7024_ = v_isSharedCheck_7032_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_7024_ == 0 {
                    v___x_7026_ = v___x_7023_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_7031_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7031_, 0 as u32, v_kernel_7019_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7031_, 1 as u32, v_native_7020_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7031_, 2 as u32, v_zetaReduce_7021_);
                    v___x_7026_ = v_reuseFailAlloc_7031_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_7027_ = (lean_unbox(v_a_7015_) as u8);
                lean_dec(v_a_7015_);
                lean_ctor_set_uint8(v___x_7026_, 3 as u32, v___x_7027_);
                if v_isShared_7018_ == 0 {
                    lean_ctor_set(v___x_7017_, 0, v___x_7026_);
                    v___x_7029_ = v___x_7017_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7030_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7030_, 0, v___x_7026_);
                    v___x_7029_ = v_reuseFailAlloc_7030_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7029_;
            }
            14 => {
                if v_isShared_7037_ == 0 {
                    v___x_7039_ = v___x_7036_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7040_, 0, v_a_7034_);
                    v___x_7039_ = v_reuseFailAlloc_7040_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7039_;
            }
            16 => {
                if v_isShared_7045_ == 0 {
                    v___x_7047_ = v___x_7044_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7048_, 0, v_a_7042_);
                    v___x_7047_ = v_reuseFailAlloc_7048_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7047_;
            }
            18 => {
                v_kernel_7058_ = lean_ctor_get_uint8(v_config_6938_, 0 as u32);
                v_zetaReduce_7059_ = lean_ctor_get_uint8(v_config_6938_, 2 as u32);
                v_revert_7060_ = lean_ctor_get_uint8(v_config_6938_, 3 as u32);
                v_isSharedCheck_7071_ = (!lean_is_exclusive(v_config_6938_)) as u8;
                if v_isSharedCheck_7071_ == 0 {
                    v___x_7062_ = v_config_6938_;
                    v_isShared_7063_ = v_isSharedCheck_7071_;
                    state = 19;
                    continue;
                } else {
                    lean_dec(v_config_6938_);
                    v___x_7062_ = lean_box(0);
                    v_isShared_7063_ = v_isSharedCheck_7071_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_7063_ == 0 {
                    v___x_7065_ = v___x_7062_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7070_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7070_, 0 as u32, v_kernel_7058_);
                    v___x_7065_ = v_reuseFailAlloc_7070_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_7066_ = (lean_unbox(v_a_7054_) as u8);
                lean_dec(v_a_7054_);
                lean_ctor_set_uint8(v___x_7065_, 1 as u32, v___x_7066_);
                lean_ctor_set_uint8(v___x_7065_, 2 as u32, v_zetaReduce_7059_);
                lean_ctor_set_uint8(v___x_7065_, 3 as u32, v_revert_7060_);
                if v_isShared_7057_ == 0 {
                    lean_ctor_set(v___x_7056_, 0, v___x_7065_);
                    v___x_7068_ = v___x_7056_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7069_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7069_, 0, v___x_7065_);
                    v___x_7068_ = v_reuseFailAlloc_7069_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7068_;
            }
            22 => {
                if v_isShared_7076_ == 0 {
                    v___x_7078_ = v___x_7075_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7079_, 0, v_a_7073_);
                    v___x_7078_ = v_reuseFailAlloc_7079_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7078_;
            }
            24 => {
                if v_isShared_7084_ == 0 {
                    v___x_7086_ = v___x_7083_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7087_, 0, v_a_7081_);
                    v___x_7086_ = v_reuseFailAlloc_7087_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7086_;
            }
            26 => {
                v_native_7097_ = lean_ctor_get_uint8(v_config_6938_, 1 as u32);
                v_zetaReduce_7098_ = lean_ctor_get_uint8(v_config_6938_, 2 as u32);
                v_revert_7099_ = lean_ctor_get_uint8(v_config_6938_, 3 as u32);
                v_isSharedCheck_7110_ = (!lean_is_exclusive(v_config_6938_)) as u8;
                if v_isSharedCheck_7110_ == 0 {
                    v___x_7101_ = v_config_6938_;
                    v_isShared_7102_ = v_isSharedCheck_7110_;
                    state = 27;
                    continue;
                } else {
                    lean_dec(v_config_6938_);
                    v___x_7101_ = lean_box(0);
                    v_isShared_7102_ = v_isSharedCheck_7110_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_7102_ == 0 {
                    v___x_7104_ = v___x_7101_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_7109_ = lean_alloc_ctor(0, 0, (4) as u32);
                    v___x_7104_ = v_reuseFailAlloc_7109_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_7105_ = (lean_unbox(v_a_7093_) as u8);
                lean_dec(v_a_7093_);
                lean_ctor_set_uint8(v___x_7104_, 0 as u32, v___x_7105_);
                lean_ctor_set_uint8(v___x_7104_, 1 as u32, v_native_7097_);
                lean_ctor_set_uint8(v___x_7104_, 2 as u32, v_zetaReduce_7098_);
                lean_ctor_set_uint8(v___x_7104_, 3 as u32, v_revert_7099_);
                if v_isShared_7096_ == 0 {
                    lean_ctor_set(v___x_7095_, 0, v___x_7104_);
                    v___x_7107_ = v___x_7095_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_7108_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7108_, 0, v___x_7104_);
                    v___x_7107_ = v_reuseFailAlloc_7108_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_7107_;
            }
            30 => {
                if v_isShared_7115_ == 0 {
                    v___x_7117_ = v___x_7114_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7118_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7118_, 0, v_a_7112_);
                    v___x_7117_ = v_reuseFailAlloc_7118_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7117_;
            }
            32 => {
                if v_isShared_7123_ == 0 {
                    v___x_7125_ = v___x_7122_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7126_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7126_, 0, v_a_7120_);
                    v___x_7125_ = v_reuseFailAlloc_7126_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7125_;
            }
            34 => {
                if v_isShared_7134_ == 0 {
                    v___x_7136_ = v___x_7133_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_7137_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7137_, 0, v_a_7131_);
                    v___x_7136_ = v_reuseFailAlloc_7137_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_7136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0___boxed(
    mut v_config_7139_: *mut LeanObject,
    mut v_item_7140_: *mut LeanObject,
    mut v___y_7141_: *mut LeanObject,
    mut v___y_7142_: *mut LeanObject,
    mut v___y_7143_: *mut LeanObject,
    mut v___y_7144_: *mut LeanObject,
    mut v___y_7145_: *mut LeanObject,
    mut v___y_7146_: *mut LeanObject,
    mut v___y_7147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7148_: *mut LeanObject = core::ptr::null_mut();
    v_res_7148_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___lam__0(v_config_7139_, v_item_7140_, v___y_7141_, v___y_7142_, v___y_7143_, v___y_7144_, v___y_7145_, v___y_7146_);
    lean_dec(v___y_7146_);
    lean_dec_ref(v___y_7145_);
    lean_dec(v___y_7144_);
    lean_dec_ref(v___y_7143_);
    lean_dec(v___y_7142_);
    lean_dec_ref(v___y_7141_);
    return v_res_7148_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(
    mut v_00_u03b1_7151_: *mut LeanObject,
    mut v___y_7152_: *mut LeanObject,
    mut v___y_7153_: *mut LeanObject,
    mut v___y_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
    mut v___y_7156_: *mut LeanObject,
    mut v___y_7157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    v___x_7159_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___redArg();
    return v___x_7159_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0___boxed(
    mut v_00_u03b1_7160_: *mut LeanObject,
    mut v___y_7161_: *mut LeanObject,
    mut v___y_7162_: *mut LeanObject,
    mut v___y_7163_: *mut LeanObject,
    mut v___y_7164_: *mut LeanObject,
    mut v___y_7165_: *mut LeanObject,
    mut v___y_7166_: *mut LeanObject,
    mut v___y_7167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7168_: *mut LeanObject = core::ptr::null_mut();
    v_res_7168_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem_spec__0_spec__0(v_00_u03b1_7160_, v___y_7161_, v___y_7162_, v___y_7163_, v___y_7164_, v___y_7165_, v___y_7166_);
    lean_dec(v___y_7166_);
    lean_dec_ref(v___y_7165_);
    lean_dec(v___y_7164_);
    lean_dec_ref(v___y_7163_);
    lean_dec(v___y_7162_);
    lean_dec_ref(v___y_7161_);
    return v_res_7168_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_7169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut LeanObject = core::ptr::null_mut();
    v___x_7169_ = lean_box(0);
    v___x_7170_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig_evalExpr___closed__5;
    v___x_7171_ = l_Lean_mkConst(v___x_7170_, v___x_7169_);
    return v___x_7171_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
    v___x_7172_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__0,
    );
    v___x_7173_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7173_, 0, v___x_7172_);
    return v___x_7173_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(
    mut v_cfg_7174_: *mut LeanObject,
    mut v_cfgItem_7175_: *mut LeanObject,
    mut v___y_7176_: *mut LeanObject,
    mut v___y_7177_: *mut LeanObject,
    mut v___y_7178_: *mut LeanObject,
    mut v___y_7179_: *mut LeanObject,
    mut v___y_7180_: *mut LeanObject,
    mut v___y_7181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7184_: *mut LeanObject = core::ptr::null_mut();
    v___x_7183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___closed__1,
    );
    v___x_7184_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v_cfg_7174_,
        v_cfgItem_7175_,
        v___x_7183_,
        v___y_7176_,
        v___y_7177_,
        v___y_7178_,
        v___y_7179_,
        v___y_7180_,
        v___y_7181_,
    );
    return v___x_7184_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0___boxed(
    mut v_cfg_7185_: *mut LeanObject,
    mut v_cfgItem_7186_: *mut LeanObject,
    mut v___y_7187_: *mut LeanObject,
    mut v___y_7188_: *mut LeanObject,
    mut v___y_7189_: *mut LeanObject,
    mut v___y_7190_: *mut LeanObject,
    mut v___y_7191_: *mut LeanObject,
    mut v___y_7192_: *mut LeanObject,
    mut v___y_7193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7194_: *mut LeanObject = core::ptr::null_mut();
    v_res_7194_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg___lam__0(
        v_cfg_7185_,
        v_cfgItem_7186_,
        v___y_7187_,
        v___y_7188_,
        v___y_7189_,
        v___y_7190_,
        v___y_7191_,
        v___y_7192_,
    );
    lean_dec(v___y_7192_);
    lean_dec_ref(v___y_7191_);
    lean_dec(v___y_7190_);
    lean_dec_ref(v___y_7189_);
    lean_dec(v___y_7188_);
    lean_dec_ref(v___y_7187_);
    lean_dec(v_cfgItem_7186_);
    return v_res_7194_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabDecideConfig___redArg(
    mut v_cfg_7196_: *mut LeanObject,
    mut v_init_7197_: *mut LeanObject,
    mut v_logExceptions_7198_: u8,
    mut v_a_7199_: *mut LeanObject,
    mut v_a_7200_: *mut LeanObject,
    mut v_a_7201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_onErr_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eval_7204_: *mut LeanObject = core::ptr::null_mut();
    v_onErr_7203_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg___closed__0;
    v_eval_7204_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_elabDecideConfig_evalConfigItem___closed__0;
    if v_logExceptions_7198_ == 0 {
        let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
        v___x_7205_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_7204_,
            v_init_7197_,
            v_cfg_7196_,
            v_onErr_7203_,
            v_logExceptions_7198_,
            v_a_7200_,
            v_a_7201_,
        );
        return v___x_7205_;
    } else {
        let mut v_recover_7206_: u8 = 0;
        let mut v___x_7207_: *mut LeanObject = core::ptr::null_mut();
        v_recover_7206_ = lean_ctor_get_uint8(
            v_a_7199_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v___x_7207_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_7204_,
            v_init_7197_,
            v_cfg_7196_,
            v_onErr_7203_,
            v_recover_7206_,
            v_a_7200_,
            v_a_7201_,
        );
        return v___x_7207_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabDecideConfig___redArg___boxed(
    mut v_cfg_7208_: *mut LeanObject,
    mut v_init_7209_: *mut LeanObject,
    mut v_logExceptions_7210_: *mut LeanObject,
    mut v_a_7211_: *mut LeanObject,
    mut v_a_7212_: *mut LeanObject,
    mut v_a_7213_: *mut LeanObject,
    mut v_a_7214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7215_: u8 = 0;
    let mut v_res_7216_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7215_ = (lean_unbox(v_logExceptions_7210_) as u8);
    v_res_7216_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(
        v_cfg_7208_,
        v_init_7209_,
        v_logExceptions_boxed_7215_,
        v_a_7211_,
        v_a_7212_,
        v_a_7213_,
    );
    lean_dec(v_a_7213_);
    lean_dec_ref(v_a_7212_);
    lean_dec_ref(v_a_7211_);
    return v_res_7216_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabDecideConfig(
    mut v_cfg_7217_: *mut LeanObject,
    mut v_init_7218_: *mut LeanObject,
    mut v_logExceptions_7219_: u8,
    mut v_a_7220_: *mut LeanObject,
    mut v_a_7221_: *mut LeanObject,
    mut v_a_7222_: *mut LeanObject,
    mut v_a_7223_: *mut LeanObject,
    mut v_a_7224_: *mut LeanObject,
    mut v_a_7225_: *mut LeanObject,
    mut v_a_7226_: *mut LeanObject,
    mut v_a_7227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7229_: *mut LeanObject = core::ptr::null_mut();
    v___x_7229_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(
        v_cfg_7217_,
        v_init_7218_,
        v_logExceptions_7219_,
        v_a_7220_,
        v_a_7226_,
        v_a_7227_,
    );
    return v___x_7229_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabDecideConfig___boxed(
    mut v_cfg_7230_: *mut LeanObject,
    mut v_init_7231_: *mut LeanObject,
    mut v_logExceptions_7232_: *mut LeanObject,
    mut v_a_7233_: *mut LeanObject,
    mut v_a_7234_: *mut LeanObject,
    mut v_a_7235_: *mut LeanObject,
    mut v_a_7236_: *mut LeanObject,
    mut v_a_7237_: *mut LeanObject,
    mut v_a_7238_: *mut LeanObject,
    mut v_a_7239_: *mut LeanObject,
    mut v_a_7240_: *mut LeanObject,
    mut v_a_7241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_7242_: u8 = 0;
    let mut v_res_7243_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_7242_ = (lean_unbox(v_logExceptions_7232_) as u8);
    v_res_7243_ = l_Lean_Elab_Tactic_elabDecideConfig(
        v_cfg_7230_,
        v_init_7231_,
        v_logExceptions_boxed_7242_,
        v_a_7233_,
        v_a_7234_,
        v_a_7235_,
        v_a_7236_,
        v_a_7237_,
        v_a_7238_,
        v_a_7239_,
        v_a_7240_,
    );
    lean_dec(v_a_7240_);
    lean_dec_ref(v_a_7239_);
    lean_dec(v_a_7238_);
    lean_dec_ref(v_a_7237_);
    lean_dec(v_a_7236_);
    lean_dec_ref(v_a_7235_);
    lean_dec(v_a_7234_);
    lean_dec_ref(v_a_7233_);
    return v_res_7243_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecide(
    mut v_stx_7250_: *mut LeanObject,
    mut v_a_7251_: *mut LeanObject,
    mut v_a_7252_: *mut LeanObject,
    mut v_a_7253_: *mut LeanObject,
    mut v_a_7254_: *mut LeanObject,
    mut v_a_7255_: *mut LeanObject,
    mut v_a_7256_: *mut LeanObject,
    mut v_a_7257_: *mut LeanObject,
    mut v_a_7258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7262_: u8 = 0;
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7271_: u8 = 0;
    let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7260_ = lean_unsigned_to_nat(1);
                v___x_7261_ = l_Lean_Syntax_getArg(v_stx_7250_, v___x_7260_);
                v___x_7262_ = 1;
                v___x_7263_ = l_Lean_Elab_Tactic_evalDecide___closed__0;
                v___x_7264_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(
                    v___x_7261_,
                    v___x_7263_,
                    v___x_7262_,
                    v_a_7251_,
                    v_a_7257_,
                    v_a_7258_,
                );
                if lean_obj_tag(v___x_7264_) == 0 {
                    v_a_7265_ = lean_ctor_get(v___x_7264_, 0);
                    lean_inc(v_a_7265_);
                    lean_dec_ref_known(v___x_7264_, 1);
                    v___x_7266_ = l_Lean_Elab_Tactic_evalDecide___closed__2;
                    v___x_7267_ = l_Lean_Elab_Tactic_evalDecideCore(
                        v___x_7266_,
                        v_a_7265_,
                        v_a_7251_,
                        v_a_7252_,
                        v_a_7253_,
                        v_a_7254_,
                        v_a_7255_,
                        v_a_7256_,
                        v_a_7257_,
                        v_a_7258_,
                    );
                    lean_dec(v_a_7265_);
                    return v___x_7267_;
                } else {
                    v_a_7268_ = lean_ctor_get(v___x_7264_, 0);
                    v_isSharedCheck_7275_ = (!lean_is_exclusive(v___x_7264_)) as u8;
                    if v_isSharedCheck_7275_ == 0 {
                        v___x_7270_ = v___x_7264_;
                        v_isShared_7271_ = v_isSharedCheck_7275_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7268_);
                        lean_dec(v___x_7264_);
                        v___x_7270_ = lean_box(0);
                        v_isShared_7271_ = v_isSharedCheck_7275_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7271_ == 0 {
                    v___x_7273_ = v___x_7270_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7274_, 0, v_a_7268_);
                    v___x_7273_ = v_reuseFailAlloc_7274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalDecide___boxed(
    mut v_stx_7276_: *mut LeanObject,
    mut v_a_7277_: *mut LeanObject,
    mut v_a_7278_: *mut LeanObject,
    mut v_a_7279_: *mut LeanObject,
    mut v_a_7280_: *mut LeanObject,
    mut v_a_7281_: *mut LeanObject,
    mut v_a_7282_: *mut LeanObject,
    mut v_a_7283_: *mut LeanObject,
    mut v_a_7284_: *mut LeanObject,
    mut v_a_7285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7286_: *mut LeanObject = core::ptr::null_mut();
    v_res_7286_ = l_Lean_Elab_Tactic_evalDecide(
        v_stx_7276_,
        v_a_7277_,
        v_a_7278_,
        v_a_7279_,
        v_a_7280_,
        v_a_7281_,
        v_a_7282_,
        v_a_7283_,
        v_a_7284_,
    );
    lean_dec(v_a_7284_);
    lean_dec_ref(v_a_7283_);
    lean_dec(v_a_7282_);
    lean_dec_ref(v_a_7281_);
    lean_dec(v_a_7280_);
    lean_dec_ref(v_a_7279_);
    lean_dec(v_a_7278_);
    lean_dec_ref(v_a_7277_);
    lean_dec(v_stx_7276_);
    return v_res_7286_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1()
-> *mut LeanObject {
    let mut v___x_7300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7304_: *mut LeanObject = core::ptr::null_mut();
    v___x_7300_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7301_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__0;
    v___x_7302_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3;
    v___x_7303_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalDecide___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7304_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7300_,
        v___x_7301_,
        v___x_7302_,
        v___x_7303_,
    );
    return v___x_7304_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___boxed(
    mut v_a_7305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7306_: *mut LeanObject = core::ptr::null_mut();
    v_res_7306_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
    return v_res_7306_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3()
-> *mut LeanObject {
    let mut v___x_7333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    v___x_7333_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1___closed__3;
    v___x_7334_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___closed__6;
    v___x_7335_ = l_Lean_addBuiltinDeclarationRanges(v___x_7333_, v___x_7334_);
    return v___x_7335_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3___boxed(
    mut v_a_7336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7337_: *mut LeanObject = core::ptr::null_mut();
    v_res_7337_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
    return v_res_7337_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalNativeDecide(
    mut v_stx_7341_: *mut LeanObject,
    mut v_a_7342_: *mut LeanObject,
    mut v_a_7343_: *mut LeanObject,
    mut v_a_7344_: *mut LeanObject,
    mut v_a_7345_: *mut LeanObject,
    mut v_a_7346_: *mut LeanObject,
    mut v_a_7347_: *mut LeanObject,
    mut v_a_7348_: *mut LeanObject,
    mut v_a_7349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: u8 = 0;
    let mut v___x_7354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kernel_7357_: u8 = 0;
    let mut v_zetaReduce_7358_: u8 = 0;
    let mut v_revert_7359_: u8 = 0;
    let mut v___x_7361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7362_: u8 = 0;
    let mut v___x_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7368_: u8 = 0;
    let mut v_a_7369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7372_: u8 = 0;
    let mut v___x_7374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7376_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7351_ = lean_unsigned_to_nat(1);
                v___x_7352_ = l_Lean_Syntax_getArg(v_stx_7341_, v___x_7351_);
                v___x_7353_ = 1;
                v___x_7354_ = l_Lean_Elab_Tactic_evalDecide___closed__0;
                v___x_7355_ = l_Lean_Elab_Tactic_elabDecideConfig___redArg(
                    v___x_7352_,
                    v___x_7354_,
                    v___x_7353_,
                    v_a_7342_,
                    v_a_7348_,
                    v_a_7349_,
                );
                if lean_obj_tag(v___x_7355_) == 0 {
                    v_a_7356_ = lean_ctor_get(v___x_7355_, 0);
                    lean_inc(v_a_7356_);
                    lean_dec_ref_known(v___x_7355_, 1);
                    v_kernel_7357_ = lean_ctor_get_uint8(v_a_7356_, 0 as u32);
                    v_zetaReduce_7358_ = lean_ctor_get_uint8(v_a_7356_, 2 as u32);
                    v_revert_7359_ = lean_ctor_get_uint8(v_a_7356_, 3 as u32);
                    v_isSharedCheck_7368_ = (!lean_is_exclusive(v_a_7356_)) as u8;
                    if v_isSharedCheck_7368_ == 0 {
                        v___x_7361_ = v_a_7356_;
                        v_isShared_7362_ = v_isSharedCheck_7368_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_a_7356_);
                        v___x_7361_ = lean_box(0);
                        v_isShared_7362_ = v_isSharedCheck_7368_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7369_ = lean_ctor_get(v___x_7355_, 0);
                    v_isSharedCheck_7376_ = (!lean_is_exclusive(v___x_7355_)) as u8;
                    if v_isSharedCheck_7376_ == 0 {
                        v___x_7371_ = v___x_7355_;
                        v_isShared_7372_ = v_isSharedCheck_7376_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7369_);
                        lean_dec(v___x_7355_);
                        v___x_7371_ = lean_box(0);
                        v_isShared_7372_ = v_isSharedCheck_7376_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7362_ == 0 {
                    v___x_7364_ = v___x_7361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7367_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7367_, 0 as u32, v_kernel_7357_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7367_, 2 as u32, v_zetaReduce_7358_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_7367_, 3 as u32, v_revert_7359_);
                    v___x_7364_ = v_reuseFailAlloc_7367_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(v___x_7364_, 1 as u32, v___x_7353_);
                v___x_7365_ = l_Lean_Elab_Tactic_evalNativeDecide___closed__1;
                v___x_7366_ = l_Lean_Elab_Tactic_evalDecideCore(
                    v___x_7365_,
                    v___x_7364_,
                    v_a_7342_,
                    v_a_7343_,
                    v_a_7344_,
                    v_a_7345_,
                    v_a_7346_,
                    v_a_7347_,
                    v_a_7348_,
                    v_a_7349_,
                );
                lean_dec_ref(v___x_7364_);
                return v___x_7366_;
            }
            3 => {
                if v_isShared_7372_ == 0 {
                    v___x_7374_ = v___x_7371_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7375_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7375_, 0, v_a_7369_);
                    v___x_7374_ = v_reuseFailAlloc_7375_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalNativeDecide___boxed(
    mut v_stx_7377_: *mut LeanObject,
    mut v_a_7378_: *mut LeanObject,
    mut v_a_7379_: *mut LeanObject,
    mut v_a_7380_: *mut LeanObject,
    mut v_a_7381_: *mut LeanObject,
    mut v_a_7382_: *mut LeanObject,
    mut v_a_7383_: *mut LeanObject,
    mut v_a_7384_: *mut LeanObject,
    mut v_a_7385_: *mut LeanObject,
    mut v_a_7386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7387_: *mut LeanObject = core::ptr::null_mut();
    v_res_7387_ = l_Lean_Elab_Tactic_evalNativeDecide(
        v_stx_7377_,
        v_a_7378_,
        v_a_7379_,
        v_a_7380_,
        v_a_7381_,
        v_a_7382_,
        v_a_7383_,
        v_a_7384_,
        v_a_7385_,
    );
    lean_dec(v_a_7385_);
    lean_dec_ref(v_a_7384_);
    lean_dec(v_a_7383_);
    lean_dec_ref(v_a_7382_);
    lean_dec(v_a_7381_);
    lean_dec_ref(v_a_7380_);
    lean_dec(v_a_7379_);
    lean_dec_ref(v_a_7378_);
    lean_dec(v_stx_7377_);
    return v_res_7387_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1()
-> *mut LeanObject {
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    v___x_7401_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_7402_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__1;
    v___x_7403_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3;
    v___x_7404_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalNativeDecide___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_7405_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7401_,
        v___x_7402_,
        v___x_7403_,
        v___x_7404_,
    );
    return v___x_7405_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___boxed(
    mut v_a_7406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7407_: *mut LeanObject = core::ptr::null_mut();
    v_res_7407_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
    return v_res_7407_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3()
-> *mut LeanObject {
    let mut v___x_7434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut LeanObject = core::ptr::null_mut();
    v___x_7434_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1___closed__3;
    v___x_7435_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___closed__6;
    v___x_7436_ = l_Lean_addBuiltinDeclarationRanges(v___x_7434_, v___x_7435_);
    return v___x_7436_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3___boxed(
    mut v_a_7437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7438_: *mut LeanObject = core::ptr::null_mut();
    v_res_7438_ = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
    return v_res_7438_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Decide(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Native(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig =
        _init_l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig();
    lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_instEvalExprDecideConfig,
    );
    res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalDecide___regBuiltin_Lean_Elab_Tactic_evalDecide_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Decide_0__Lean_Elab_Tactic_evalNativeDecide___regBuiltin_Lean_Elab_Tactic_evalNativeDecide_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Decide(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Decide(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Native(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Decide(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Decide(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Decide(builtin);
}
