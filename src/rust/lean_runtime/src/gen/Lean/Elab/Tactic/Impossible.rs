// Lean compiler output
// Module: Lean.Elab.Tactic.Impossible
// Imports: Lean.Elab.Tactic.Basic Lean.Elab.ConfigEval Lean.Meta.Tactic.Cleanup Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Closure
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_DeclNameGenerator_mkUniqueName, l_Lean_Elab_async, l_Lean_Exception_isRuntime,
    l_Lean_diagnostics, l_Lean_mkArrow,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
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
    initialize_Lean_Elab_Tactic_Basic, l_Lean_Elab_Tactic_done, l_Lean_Elab_Tactic_evalTactic,
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_getUnsolvedGoals,
    l_Lean_Elab_Tactic_mkInitialTacticInfo, l_Lean_Elab_Tactic_setGoals___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_admitGoal,
    runtime_initialize_Lean_Elab_Tactic_Basic,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType___boxed, l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Kernel_enableDiag, l_Lean_Kernel_isDiagnosticsEnabled,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_hasLevelMVar, l_Lean_Expr_hasMVar,
    l_Lean_Expr_mvarId_x21, l_Lean_instInhabitedExpr, l_Lean_mkConst, l_Lean_mkMVar, l_Lean_mkNot,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::l_Lean_LocalContext_getFVarIds;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_getDecl,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkFreshExprMVarAt, l_Lean_Meta_mkFreshLevelMVar,
};
use crate::r#gen::Lean::Meta::Closure::{
    initialize_Lean_Meta_Closure, l_Lean_Meta_Closure_mkValueTypeClosure,
    runtime_initialize_Lean_Meta_Closure,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Tactic::Cleanup::{
    initialize_Lean_Meta_Tactic_Cleanup,
    l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore,
    runtime_initialize_Lean_Meta_Tactic_Cleanup,
};
use crate::r#gen::Lean::Meta::Tactic::Intro::{
    initialize_Lean_Meta_Tactic_Intro, l_Lean_Meta_introNCore,
    runtime_initialize_Lean_Meta_Tactic_Intro,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::{
    initialize_Lean_Meta_Tactic_Revert, l_Lean_MVarId_revert,
    runtime_initialize_Lean_Meta_Tactic_Revert,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParamsArray;
use crate::r#gen::Lean::Util::RecDepth::l_Lean_maxRecDepth;
use crate::r#gen::Lean::Util::Sorry::{l_Lean_Expr_hasSorry, l_Lean_Expr_hasSyntheticSorry};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_9, lean_apply_10, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 97, 108, 115, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__0_value) as *mut LeanObject,907667957179513571 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [120, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__0_value) as *mut LeanObject,13655884332201764339 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 114, 117, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__1_value) as *mut LeanObject,11870096045526947150 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__4_value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___boxed as *const core::ffi::c_void, m_arity: 10, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [73, 109, 112, 111, 115, 115, 105, 98, 108, 101, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value) as *mut LeanObject,3925214266257733826 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 96, 115, 111, 114, 114, 121, 96, 58, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [108, 101, 118, 101, 108, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__4_value) as *mut LeanObject,3925214266257733826 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject,3823243780028431886 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalImpossible___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalImpossible___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalImpossible___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalImpossible___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalImpossible___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalImpossible___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalImpossible___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_evalImpossible___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalImpossible___closed__8_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_Tactic_evalImpossible___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalImpossible___closed__8_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalImpossible___closed__9_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [95, 105, 109, 112, 111, 115, 115, 105, 98, 108, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalImpossible___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalImpossible___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalImpossible___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalImpossible___closed__9_value)
                as *mut LeanObject,
            12438387699751937112 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalImpossible___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalImpossible___closed__10_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_evalImpossible___closed__11_value: LeanStringObject<51> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 51,
        m_capacity: 51,
        m_length: 50,
        m_data: [
            96, 105, 109, 112, 111, 115, 115, 105, 98, 108, 101, 96, 58, 32, 103, 111, 97, 108, 32,
            99, 111, 110, 116, 97, 105, 110, 115, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32,
            109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalImpossible___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalImpossible___closed__11_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_evalImpossible___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_evalImpossible___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 109, 112, 111, 115, 115, 105, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__0_value) as *mut LeanObject,8139708910801068529 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 118, 97, 108, 73, 109, 112, 111, 115, 115, 105, 98, 108, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__2_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__3_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__3_value) as *mut LeanObject,8153502899169889411 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0(
    mut v_k_2244_: *mut LeanObject,
    mut v_b_2245_: *mut LeanObject,
    mut v_c_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2250_);
    lean_inc_ref(v___y_2249_);
    lean_inc(v___y_2248_);
    lean_inc_ref(v___y_2247_);
    v___x_2252_ = lean_apply_7(
        v_k_2244_,
        v_b_2245_,
        v_c_2246_,
        v___y_2247_,
        v___y_2248_,
        v___y_2249_,
        v___y_2250_,
        lean_box(0),
    );
    return v___x_2252_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0___boxed(
    mut v_k_2253_: *mut LeanObject,
    mut v_b_2254_: *mut LeanObject,
    mut v_c_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2261_: *mut LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0(v_k_2253_, v_b_2254_, v_c_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
    lean_dec(v___y_2259_);
    lean_dec_ref(v___y_2258_);
    lean_dec(v___y_2257_);
    lean_dec_ref(v___y_2256_);
    return v_res_2261_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(
    mut v_type_2262_: *mut LeanObject,
    mut v_maxFVars_x3f_2263_: *mut LeanObject,
    mut v_k_2264_: *mut LeanObject,
    mut v_cleanupAnnotations_2265_: u8,
    mut v_whnfType_2266_: u8,
    mut v___y_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v_a_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2289_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2272_ = lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_2272_, 0, v_k_2264_);
                v___x_2273_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    lean_box(0),
                    v_type_2262_,
                    v_maxFVars_x3f_2263_,
                    v___f_2272_,
                    v_cleanupAnnotations_2265_,
                    v_whnfType_2266_,
                    v___y_2267_,
                    v___y_2268_,
                    v___y_2269_,
                    v___y_2270_,
                );
                if lean_obj_tag(v___x_2273_) == 0 {
                    v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
                    v_isSharedCheck_2281_ = (!lean_is_exclusive(v___x_2273_)) as u8;
                    if v_isSharedCheck_2281_ == 0 {
                        v___x_2276_ = v___x_2273_;
                        v_isShared_2277_ = v_isSharedCheck_2281_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2274_);
                        lean_dec(v___x_2273_);
                        v___x_2276_ = lean_box(0);
                        v_isShared_2277_ = v_isSharedCheck_2281_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2282_ = lean_ctor_get(v___x_2273_, 0);
                    v_isSharedCheck_2289_ = (!lean_is_exclusive(v___x_2273_)) as u8;
                    if v_isSharedCheck_2289_ == 0 {
                        v___x_2284_ = v___x_2273_;
                        v_isShared_2285_ = v_isSharedCheck_2289_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2282_);
                        lean_dec(v___x_2273_);
                        v___x_2284_ = lean_box(0);
                        v_isShared_2285_ = v_isSharedCheck_2289_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2277_ == 0 {
                    v___x_2279_ = v___x_2276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
                    v___x_2279_ = v_reuseFailAlloc_2280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2279_;
            }
            3 => {
                if v_isShared_2285_ == 0 {
                    v___x_2287_ = v___x_2284_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
                    v___x_2287_ = v_reuseFailAlloc_2288_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg___boxed(
    mut v_type_2290_: *mut LeanObject,
    mut v_maxFVars_x3f_2291_: *mut LeanObject,
    mut v_k_2292_: *mut LeanObject,
    mut v_cleanupAnnotations_2293_: *mut LeanObject,
    mut v_whnfType_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2300_: u8 = 0;
    let mut v_whnfType_boxed_2301_: u8 = 0;
    let mut v_res_2302_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2300_ = (lean_unbox(v_cleanupAnnotations_2293_) as u8);
    v_whnfType_boxed_2301_ = (lean_unbox(v_whnfType_2294_) as u8);
    v_res_2302_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(v_type_2290_, v_maxFVars_x3f_2291_, v_k_2292_, v_cleanupAnnotations_boxed_2300_, v_whnfType_boxed_2301_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
    lean_dec(v___y_2298_);
    lean_dec_ref(v___y_2297_);
    lean_dec(v___y_2296_);
    lean_dec_ref(v___y_2295_);
    return v_res_2302_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0(
    mut v_00_u03b1_2303_: *mut LeanObject,
    mut v_type_2304_: *mut LeanObject,
    mut v_maxFVars_x3f_2305_: *mut LeanObject,
    mut v_k_2306_: *mut LeanObject,
    mut v_cleanupAnnotations_2307_: u8,
    mut v_whnfType_2308_: u8,
    mut v___y_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    v___x_2314_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(v_type_2304_, v_maxFVars_x3f_2305_, v_k_2306_, v_cleanupAnnotations_2307_, v_whnfType_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
    return v___x_2314_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___boxed(
    mut v_00_u03b1_2315_: *mut LeanObject,
    mut v_type_2316_: *mut LeanObject,
    mut v_maxFVars_x3f_2317_: *mut LeanObject,
    mut v_k_2318_: *mut LeanObject,
    mut v_cleanupAnnotations_2319_: *mut LeanObject,
    mut v_whnfType_2320_: *mut LeanObject,
    mut v___y_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_2326_: u8 = 0;
    let mut v_whnfType_boxed_2327_: u8 = 0;
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2326_ = (lean_unbox(v_cleanupAnnotations_2319_) as u8);
    v_whnfType_boxed_2327_ = (lean_unbox(v_whnfType_2320_) as u8);
    v_res_2328_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0(v_00_u03b1_2315_, v_type_2316_, v_maxFVars_x3f_2317_, v_k_2318_, v_cleanupAnnotations_boxed_2326_, v_whnfType_boxed_2327_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
    lean_dec(v___y_2324_);
    lean_dec_ref(v___y_2323_);
    lean_dec(v___y_2322_);
    lean_dec_ref(v___y_2321_);
    return v_res_2328_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(
    mut v_mvarId_2329_: *mut LeanObject,
    mut v_x_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
    mut v___y_2333_: *mut LeanObject,
    mut v___y_2334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2340_: u8 = 0;
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2344_: u8 = 0;
    let mut v_a_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2348_: u8 = 0;
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2336_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2329_,
                    v_x_2330_,
                    v___y_2331_,
                    v___y_2332_,
                    v___y_2333_,
                    v___y_2334_,
                );
                if lean_obj_tag(v___x_2336_) == 0 {
                    v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
                    v_isSharedCheck_2344_ = (!lean_is_exclusive(v___x_2336_)) as u8;
                    if v_isSharedCheck_2344_ == 0 {
                        v___x_2339_ = v___x_2336_;
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2337_);
                        lean_dec(v___x_2336_);
                        v___x_2339_ = lean_box(0);
                        v_isShared_2340_ = v_isSharedCheck_2344_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2345_ = lean_ctor_get(v___x_2336_, 0);
                    v_isSharedCheck_2352_ = (!lean_is_exclusive(v___x_2336_)) as u8;
                    if v_isSharedCheck_2352_ == 0 {
                        v___x_2347_ = v___x_2336_;
                        v_isShared_2348_ = v_isSharedCheck_2352_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2345_);
                        lean_dec(v___x_2336_);
                        v___x_2347_ = lean_box(0);
                        v_isShared_2348_ = v_isSharedCheck_2352_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2340_ == 0 {
                    v___x_2342_ = v___x_2339_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
                    v___x_2342_ = v_reuseFailAlloc_2343_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2342_;
            }
            3 => {
                if v_isShared_2348_ == 0 {
                    v___x_2350_ = v___x_2347_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
                    v___x_2350_ = v_reuseFailAlloc_2351_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg___boxed(
    mut v_mvarId_2353_: *mut LeanObject,
    mut v_x_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2360_: *mut LeanObject = core::ptr::null_mut();
    v_res_2360_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(v_mvarId_2353_, v_x_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
    lean_dec(v___y_2358_);
    lean_dec_ref(v___y_2357_);
    lean_dec(v___y_2356_);
    lean_dec_ref(v___y_2355_);
    return v_res_2360_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3(
    mut v_00_u03b1_2361_: *mut LeanObject,
    mut v_mvarId_2362_: *mut LeanObject,
    mut v_x_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
    mut v___y_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    v___x_2369_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(v_mvarId_2362_, v_x_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
    return v___x_2369_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___boxed(
    mut v_00_u03b1_2370_: *mut LeanObject,
    mut v_mvarId_2371_: *mut LeanObject,
    mut v_x_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
    mut v___y_2374_: *mut LeanObject,
    mut v___y_2375_: *mut LeanObject,
    mut v___y_2376_: *mut LeanObject,
    mut v___y_2377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2378_: *mut LeanObject = core::ptr::null_mut();
    v_res_2378_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3(v_00_u03b1_2370_, v_mvarId_2371_, v_x_2372_, v___y_2373_, v___y_2374_, v___y_2375_, v___y_2376_);
    lean_dec(v___y_2376_);
    lean_dec_ref(v___y_2375_);
    lean_dec(v___y_2374_);
    lean_dec_ref(v___y_2373_);
    return v_res_2378_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0(
    mut v___x_2382_: u8,
    mut v___x_2383_: u8,
    mut v___x_2384_: *mut LeanObject,
    mut v_ms_2385_: *mut LeanObject,
    mut v_revBody_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_negBody_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2411_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2415_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_revBody_2386_);
                v___x_2400_ = l_Lean_Meta_isProp(
                    v_revBody_2386_,
                    v___y_2387_,
                    v___y_2388_,
                    v___y_2389_,
                    v___y_2390_,
                );
                if lean_obj_tag(v___x_2400_) == 0 {
                    v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
                    lean_inc(v_a_2401_);
                    lean_dec_ref_known(v___x_2400_, 1);
                    v___x_2402_ = (lean_unbox(v_a_2401_) as u8);
                    lean_dec(v_a_2401_);
                    if v___x_2402_ == 0 {
                        v___x_2403_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___closed__1;
                        v___x_2404_ = l_Lean_mkConst(v___x_2403_, v___x_2384_);
                        v___x_2405_ =
                            l_Lean_mkArrow(v_revBody_2386_, v___x_2404_, v___y_2389_, v___y_2390_);
                        if lean_obj_tag(v___x_2405_) == 0 {
                            v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
                            lean_inc(v_a_2406_);
                            lean_dec_ref_known(v___x_2405_, 1);
                            v_negBody_2393_ = v_a_2406_;
                            v___y_2394_ = v___y_2387_;
                            v___y_2395_ = v___y_2388_;
                            v___y_2396_ = v___y_2389_;
                            v___y_2397_ = v___y_2390_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_2405_;
                        }
                    } else {
                        lean_dec(v___x_2384_);
                        v___x_2407_ = l_Lean_mkNot(v_revBody_2386_);
                        v_negBody_2393_ = v___x_2407_;
                        v___y_2394_ = v___y_2387_;
                        v___y_2395_ = v___y_2388_;
                        v___y_2396_ = v___y_2389_;
                        v___y_2397_ = v___y_2390_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_revBody_2386_);
                    lean_dec(v___x_2384_);
                    v_a_2408_ = lean_ctor_get(v___x_2400_, 0);
                    v_isSharedCheck_2415_ = (!lean_is_exclusive(v___x_2400_)) as u8;
                    if v_isSharedCheck_2415_ == 0 {
                        v___x_2410_ = v___x_2400_;
                        v_isShared_2411_ = v_isSharedCheck_2415_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2408_);
                        lean_dec(v___x_2400_);
                        v___x_2410_ = lean_box(0);
                        v_isShared_2411_ = v_isSharedCheck_2415_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2398_ = 1;
                v___x_2399_ = l_Lean_Meta_mkForallFVars(
                    v_ms_2385_,
                    v_negBody_2393_,
                    v___x_2382_,
                    v___x_2383_,
                    v___x_2383_,
                    v___x_2398_,
                    v___y_2394_,
                    v___y_2395_,
                    v___y_2396_,
                    v___y_2397_,
                );
                return v___x_2399_;
            }
            2 => {
                if v_isShared_2411_ == 0 {
                    v___x_2413_ = v___x_2410_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
                    v___x_2413_ = v_reuseFailAlloc_2414_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2413_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0___boxed(
    mut v___x_2416_: *mut LeanObject,
    mut v___x_2417_: *mut LeanObject,
    mut v___x_2418_: *mut LeanObject,
    mut v_ms_2419_: *mut LeanObject,
    mut v_revBody_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4477__boxed_2426_: u8 = 0;
    let mut v___x_4478__boxed_2427_: u8 = 0;
    let mut v_res_2428_: *mut LeanObject = core::ptr::null_mut();
    v___x_4477__boxed_2426_ = (lean_unbox(v___x_2416_) as u8);
    v___x_4478__boxed_2427_ = (lean_unbox(v___x_2417_) as u8);
    v_res_2428_ =
        l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__0(
            v___x_4477__boxed_2426_,
            v___x_4478__boxed_2427_,
            v___x_2418_,
            v_ms_2419_,
            v_revBody_2420_,
            v___y_2421_,
            v___y_2422_,
            v___y_2423_,
            v___y_2424_,
        );
    lean_dec(v___y_2424_);
    lean_dec_ref(v___y_2423_);
    lean_dec(v___y_2422_);
    lean_dec_ref(v___y_2421_);
    lean_dec_ref(v_ms_2419_);
    return v_res_2428_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(
    mut v_sz_2429_: usize,
    mut v_i_2430_: usize,
    mut v_bs_2431_: *mut LeanObject,
    mut v___y_2432_: *mut LeanObject,
    mut v___y_2433_: *mut LeanObject,
    mut v___y_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2437_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2437_ = lean_usize_dec_lt(v_i_2430_, v_sz_2429_);
                if v___x_2437_ == 0 {
                    v___x_2438_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2438_, 0, v_bs_2431_);
                    return v___x_2438_;
                } else {
                    v___x_2439_ = l_Lean_Meta_mkFreshLevelMVar(
                        v___y_2432_,
                        v___y_2433_,
                        v___y_2434_,
                        v___y_2435_,
                    );
                    if lean_obj_tag(v___x_2439_) == 0 {
                        v_a_2440_ = lean_ctor_get(v___x_2439_, 0);
                        lean_inc(v_a_2440_);
                        lean_dec_ref_known(v___x_2439_, 1);
                        v___x_2441_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2442_ = lean_array_uset(v_bs_2431_, v_i_2430_, v___x_2441_);
                        v___x_2443_ = 1usize;
                        v___x_2444_ = lean_usize_add(v_i_2430_, v___x_2443_);
                        v___x_2445_ = lean_array_uset(v_bs_x27_2442_, v_i_2430_, v_a_2440_);
                        v_i_2430_ = v___x_2444_;
                        v_bs_2431_ = v___x_2445_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2431_);
                        v_a_2447_ = lean_ctor_get(v___x_2439_, 0);
                        v_isSharedCheck_2454_ = (!lean_is_exclusive(v___x_2439_)) as u8;
                        if v_isSharedCheck_2454_ == 0 {
                            v___x_2449_ = v___x_2439_;
                            v_isShared_2450_ = v_isSharedCheck_2454_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2447_);
                            lean_dec(v___x_2439_);
                            v___x_2449_ = lean_box(0);
                            v_isShared_2450_ = v_isSharedCheck_2454_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2450_ == 0 {
                    v___x_2452_ = v___x_2449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_a_2447_);
                    v___x_2452_ = v_reuseFailAlloc_2453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2___boxed(
    mut v_sz_2455_: *mut LeanObject,
    mut v_i_2456_: *mut LeanObject,
    mut v_bs_2457_: *mut LeanObject,
    mut v___y_2458_: *mut LeanObject,
    mut v___y_2459_: *mut LeanObject,
    mut v___y_2460_: *mut LeanObject,
    mut v___y_2461_: *mut LeanObject,
    mut v___y_2462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2463_: usize = 0;
    let mut v_i_boxed_2464_: usize = 0;
    let mut v_res_2465_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2463_ = lean_unbox_usize(v_sz_2455_);
    lean_dec(v_sz_2455_);
    v_i_boxed_2464_ = lean_unbox_usize(v_i_2456_);
    lean_dec(v_i_2456_);
    v_res_2465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(v_sz_boxed_2463_, v_i_boxed_2464_, v_bs_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
    lean_dec(v___y_2461_);
    lean_dec_ref(v___y_2460_);
    lean_dec(v___y_2459_);
    lean_dec_ref(v___y_2458_);
    return v_res_2465_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(
    mut v_sz_2469_: usize,
    mut v_i_2470_: usize,
    mut v_bs_2471_: *mut LeanObject,
    mut v___y_2472_: *mut LeanObject,
    mut v___y_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2477_: u8 = 0;
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: usize = 0;
    let mut v___x_2485_: usize = 0;
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userName_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2477_ = lean_usize_dec_lt(v_i_2470_, v_sz_2469_);
                if v___x_2477_ == 0 {
                    v___x_2478_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2478_, 0, v_bs_2471_);
                    return v___x_2478_;
                } else {
                    v_v_2479_ = lean_array_uget(v_bs_2471_, v_i_2470_);
                    v___x_2480_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2481_ = lean_array_uset(v_bs_2471_, v_i_2470_, v___x_2480_);
                    if lean_obj_tag(v_v_2479_) == 2 {
                        v_mvarId_2488_ = lean_ctor_get(v_v_2479_, 0);
                        lean_inc(v_mvarId_2488_);
                        lean_dec_ref_known(v_v_2479_, 1);
                        v___x_2489_ = l_Lean_MVarId_getDecl(
                            v_mvarId_2488_,
                            v___y_2472_,
                            v___y_2473_,
                            v___y_2474_,
                            v___y_2475_,
                        );
                        if lean_obj_tag(v___x_2489_) == 0 {
                            v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
                            lean_inc(v_a_2490_);
                            lean_dec_ref_known(v___x_2489_, 1);
                            v_userName_2491_ = lean_ctor_get(v_a_2490_, 0);
                            lean_inc(v_userName_2491_);
                            lean_dec(v_a_2490_);
                            v___x_2492_ = l_Lean_Name_isAnonymous(v_userName_2491_);
                            if v___x_2492_ == 0 {
                                v_a_2483_ = v_userName_2491_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_userName_2491_);
                                v___x_2493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1;
                                v_a_2483_ = v___x_2493_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_bs_x27_2481_);
                            v_a_2494_ = lean_ctor_get(v___x_2489_, 0);
                            v_isSharedCheck_2501_ = (!lean_is_exclusive(v___x_2489_)) as u8;
                            if v_isSharedCheck_2501_ == 0 {
                                v___x_2496_ = v___x_2489_;
                                v_isShared_2497_ = v_isSharedCheck_2501_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2494_);
                                lean_dec(v___x_2489_);
                                v___x_2496_ = lean_box(0);
                                v_isShared_2497_ = v_isSharedCheck_2501_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_v_2479_);
                        v___x_2502_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___closed__1;
                        v_a_2483_ = v___x_2502_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2484_ = 1usize;
                v___x_2485_ = lean_usize_add(v_i_2470_, v___x_2484_);
                v___x_2486_ = lean_array_uset(v_bs_x27_2481_, v_i_2470_, v_a_2483_);
                v_i_2470_ = v___x_2485_;
                v_bs_2471_ = v___x_2486_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_2497_ == 0 {
                    v___x_2499_ = v___x_2496_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1___boxed(
    mut v_sz_2503_: *mut LeanObject,
    mut v_i_2504_: *mut LeanObject,
    mut v_bs_2505_: *mut LeanObject,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v___y_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2511_: usize = 0;
    let mut v_i_boxed_2512_: usize = 0;
    let mut v_res_2513_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2511_ = lean_unbox_usize(v_sz_2503_);
    lean_dec(v_sz_2503_);
    v_i_boxed_2512_ = lean_unbox_usize(v_i_2504_);
    lean_dec(v_i_2504_);
    v_res_2513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(v_sz_boxed_2511_, v_i_boxed_2512_, v_bs_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
    lean_dec(v___y_2509_);
    lean_dec_ref(v___y_2508_);
    lean_dec(v___y_2507_);
    lean_dec_ref(v___y_2506_);
    return v_res_2513_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2519_ = lean_box(0);
    v___x_2520_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__2;
    v___x_2521_ = l_Lean_mkConst(v___x_2520_, v___x_2519_);
    return v___x_2521_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1(
    mut v_goalType_2528_: *mut LeanObject,
    mut v___x_2529_: *mut LeanObject,
    mut v_cfg_2530_: u8,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: u8 = 0;
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rTypeLevels_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprArgs_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2574_: usize = 0;
    let mut v___x_2575_: usize = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2587_: u8 = 0;
    let mut v_a_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2595_: u8 = 0;
    let mut v_a_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2599_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2603_: u8 = 0;
    let mut v_levelArgs_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2606_: usize = 0;
    let mut v___x_2607_: usize = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2613_: u8 = 0;
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v_a_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v_a_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2633_: u8 = 0;
    let mut v_isSharedCheck_2634_: u8 = 0;
    let mut v_unused_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v_a_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut v_a_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2655_: u8 = 0;
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_a_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2663_: u8 = 0;
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2667_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2536_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v_goalType_2528_,
                    v___x_2529_,
                    v___y_2531_,
                    v___y_2532_,
                    v___y_2533_,
                    v___y_2534_,
                );
                if lean_obj_tag(v___x_2536_) == 0 {
                    v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
                    lean_inc(v_a_2537_);
                    lean_dec_ref_known(v___x_2536_, 1);
                    v___x_2538_ = l_Lean_Expr_mvarId_x21(v_a_2537_);
                    lean_dec(v_a_2537_);
                    v___x_2539_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__0;
                    v___x_2540_ = 1;
                    v___x_2541_ = l___private_Lean_Meta_Tactic_Cleanup_0__Lean_Meta_cleanupCore(
                        v___x_2538_,
                        v___x_2539_,
                        v___x_2540_,
                        v___y_2531_,
                        v___y_2532_,
                        v___y_2533_,
                        v___y_2534_,
                    );
                    if lean_obj_tag(v___x_2541_) == 0 {
                        v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
                        lean_inc_n(v_a_2542_, 2);
                        lean_dec_ref_known(v___x_2541_, 1);
                        v___x_2543_ = l_Lean_MVarId_getDecl(
                            v_a_2542_,
                            v___y_2531_,
                            v___y_2532_,
                            v___y_2533_,
                            v___y_2534_,
                        );
                        if lean_obj_tag(v___x_2543_) == 0 {
                            v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
                            lean_inc(v_a_2544_);
                            lean_dec_ref_known(v___x_2543_, 1);
                            v_lctx_2545_ = lean_ctor_get(v_a_2544_, 1);
                            lean_inc_ref(v_lctx_2545_);
                            lean_dec(v_a_2544_);
                            v___x_2546_ = l_Lean_LocalContext_getFVarIds(v_lctx_2545_);
                            lean_dec_ref(v_lctx_2545_);
                            v___x_2547_ = 0;
                            v___x_2548_ = l_Lean_MVarId_revert(
                                v_a_2542_,
                                v___x_2546_,
                                v___x_2547_,
                                v___x_2540_,
                                v___y_2531_,
                                v___y_2532_,
                                v___y_2533_,
                                v___y_2534_,
                            );
                            if lean_obj_tag(v___x_2548_) == 0 {
                                v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
                                lean_inc(v_a_2549_);
                                lean_dec_ref_known(v___x_2548_, 1);
                                v_snd_2550_ = lean_ctor_get(v_a_2549_, 1);
                                v_isSharedCheck_2634_ = (!lean_is_exclusive(v_a_2549_)) as u8;
                                if v_isSharedCheck_2634_ == 0 {
                                    v_unused_2635_ = lean_ctor_get(v_a_2549_, 0);
                                    lean_dec(v_unused_2635_);
                                    v___x_2552_ = v_a_2549_;
                                    v_isShared_2553_ = v_isSharedCheck_2634_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_snd_2550_);
                                    lean_dec(v_a_2549_);
                                    v___x_2552_ = lean_box(0);
                                    v_isShared_2553_ = v_isSharedCheck_2634_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_2636_ = lean_ctor_get(v___x_2548_, 0);
                                v_isSharedCheck_2643_ = (!lean_is_exclusive(v___x_2548_)) as u8;
                                if v_isSharedCheck_2643_ == 0 {
                                    v___x_2638_ = v___x_2548_;
                                    v_isShared_2639_ = v_isSharedCheck_2643_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_2636_);
                                    lean_dec(v___x_2548_);
                                    v___x_2638_ = lean_box(0);
                                    v_isShared_2639_ = v_isSharedCheck_2643_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2542_);
                            v_a_2644_ = lean_ctor_get(v___x_2543_, 0);
                            v_isSharedCheck_2651_ = (!lean_is_exclusive(v___x_2543_)) as u8;
                            if v_isSharedCheck_2651_ == 0 {
                                v___x_2646_ = v___x_2543_;
                                v_isShared_2647_ = v_isSharedCheck_2651_;
                                state = 18;
                                continue;
                            } else {
                                lean_inc(v_a_2644_);
                                lean_dec(v___x_2543_);
                                v___x_2646_ = lean_box(0);
                                v_isShared_2647_ = v_isSharedCheck_2651_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        v_a_2652_ = lean_ctor_get(v___x_2541_, 0);
                        v_isSharedCheck_2659_ = (!lean_is_exclusive(v___x_2541_)) as u8;
                        if v_isSharedCheck_2659_ == 0 {
                            v___x_2654_ = v___x_2541_;
                            v_isShared_2655_ = v_isSharedCheck_2659_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_2652_);
                            lean_dec(v___x_2541_);
                            v___x_2654_ = lean_box(0);
                            v_isShared_2655_ = v_isSharedCheck_2659_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    v_a_2660_ = lean_ctor_get(v___x_2536_, 0);
                    v_isSharedCheck_2667_ = (!lean_is_exclusive(v___x_2536_)) as u8;
                    if v_isSharedCheck_2667_ == 0 {
                        v___x_2662_ = v___x_2536_;
                        v_isShared_2663_ = v_isSharedCheck_2667_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_2660_);
                        lean_dec(v___x_2536_);
                        v___x_2662_ = lean_box(0);
                        v_isShared_2663_ = v_isSharedCheck_2667_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2554_ = l_Lean_MVarId_getType(
                    v_snd_2550_,
                    v___y_2531_,
                    v___y_2532_,
                    v___y_2533_,
                    v___y_2534_,
                );
                if lean_obj_tag(v___x_2554_) == 0 {
                    v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
                    lean_inc(v_a_2555_);
                    lean_dec_ref_known(v___x_2554_, 1);
                    v___x_2556_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3_once), _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__3);
                    v___x_2557_ = l_Lean_Meta_Closure_mkValueTypeClosure(
                        v_a_2555_,
                        v___x_2556_,
                        v___x_2547_,
                        v___y_2531_,
                        v___y_2532_,
                        v___y_2533_,
                        v___y_2534_,
                    );
                    if lean_obj_tag(v___x_2557_) == 0 {
                        v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
                        lean_inc(v_a_2558_);
                        lean_dec_ref_known(v___x_2557_, 1);
                        v___f_2559_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___closed__4;
                        if v_cfg_2530_ == 0 {
                            v_levelArgs_2604_ = lean_ctor_get(v_a_2558_, 3);
                            lean_inc_ref(v_levelArgs_2604_);
                            v_rTypeLevels_2561_ = v_levelArgs_2604_;
                            v___y_2562_ = v___y_2531_;
                            v___y_2563_ = v___y_2532_;
                            v___y_2564_ = v___y_2533_;
                            v___y_2565_ = v___y_2534_;
                            state = 2;
                            continue;
                        } else {
                            v_levelParams_2605_ = lean_ctor_get(v_a_2558_, 0);
                            v_sz_2606_ = lean_array_size(v_levelParams_2605_);
                            v___x_2607_ = 0usize;
                            lean_inc_ref(v_levelParams_2605_);
                            v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__2(v_sz_2606_, v___x_2607_, v_levelParams_2605_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
                            if lean_obj_tag(v___x_2608_) == 0 {
                                v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
                                lean_inc(v_a_2609_);
                                lean_dec_ref_known(v___x_2608_, 1);
                                v_rTypeLevels_2561_ = v_a_2609_;
                                v___y_2562_ = v___y_2531_;
                                v___y_2563_ = v___y_2532_;
                                v___y_2564_ = v___y_2533_;
                                v___y_2565_ = v___y_2534_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_2558_);
                                lean_del_object(v___x_2552_);
                                v_a_2610_ = lean_ctor_get(v___x_2608_, 0);
                                v_isSharedCheck_2617_ = (!lean_is_exclusive(v___x_2608_)) as u8;
                                if v_isSharedCheck_2617_ == 0 {
                                    v___x_2612_ = v___x_2608_;
                                    v_isShared_2613_ = v_isSharedCheck_2617_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_2610_);
                                    lean_dec(v___x_2608_);
                                    v___x_2612_ = lean_box(0);
                                    v_isShared_2613_ = v_isSharedCheck_2617_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_2552_);
                        v_a_2618_ = lean_ctor_get(v___x_2557_, 0);
                        v_isSharedCheck_2625_ = (!lean_is_exclusive(v___x_2557_)) as u8;
                        if v_isSharedCheck_2625_ == 0 {
                            v___x_2620_ = v___x_2557_;
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2618_);
                            lean_dec(v___x_2557_);
                            v___x_2620_ = lean_box(0);
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2552_);
                    v_a_2626_ = lean_ctor_get(v___x_2554_, 0);
                    v_isSharedCheck_2633_ = (!lean_is_exclusive(v___x_2554_)) as u8;
                    if v_isSharedCheck_2633_ == 0 {
                        v___x_2628_ = v___x_2554_;
                        v_isShared_2629_ = v_isSharedCheck_2633_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2626_);
                        lean_dec(v___x_2554_);
                        v___x_2628_ = lean_box(0);
                        v_isShared_2629_ = v_isSharedCheck_2633_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v_levelParams_2566_ = lean_ctor_get(v_a_2558_, 0);
                lean_inc_ref(v_levelParams_2566_);
                v_type_2567_ = lean_ctor_get(v_a_2558_, 1);
                lean_inc_ref(v_type_2567_);
                v_exprArgs_2568_ = lean_ctor_get(v_a_2558_, 4);
                lean_inc_ref(v_exprArgs_2568_);
                lean_dec(v_a_2558_);
                v___x_2569_ = l_Lean_Expr_instantiateLevelParamsArray(
                    v_type_2567_,
                    v_levelParams_2566_,
                    v_rTypeLevels_2561_,
                );
                lean_dec_ref(v_type_2567_);
                v___x_2570_ = lean_array_get_size(v_exprArgs_2568_);
                v___x_2571_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2571_, 0, v___x_2570_);
                v___x_2572_ = l_Lean_Meta_forallBoundedTelescope___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__0___redArg(v___x_2569_, v___x_2571_, v___f_2559_, v___x_2547_, v___x_2547_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
                if lean_obj_tag(v___x_2572_) == 0 {
                    v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
                    lean_inc(v_a_2573_);
                    lean_dec_ref_known(v___x_2572_, 1);
                    v_sz_2574_ = lean_array_size(v_exprArgs_2568_);
                    v___x_2575_ = 0usize;
                    v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__1(v_sz_2574_, v___x_2575_, v_exprArgs_2568_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
                    if lean_obj_tag(v___x_2576_) == 0 {
                        v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
                        v_isSharedCheck_2587_ = (!lean_is_exclusive(v___x_2576_)) as u8;
                        if v_isSharedCheck_2587_ == 0 {
                            v___x_2579_ = v___x_2576_;
                            v_isShared_2580_ = v_isSharedCheck_2587_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2577_);
                            lean_dec(v___x_2576_);
                            v___x_2579_ = lean_box(0);
                            v_isShared_2580_ = v_isSharedCheck_2587_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2573_);
                        lean_del_object(v___x_2552_);
                        v_a_2588_ = lean_ctor_get(v___x_2576_, 0);
                        v_isSharedCheck_2595_ = (!lean_is_exclusive(v___x_2576_)) as u8;
                        if v_isSharedCheck_2595_ == 0 {
                            v___x_2590_ = v___x_2576_;
                            v_isShared_2591_ = v_isSharedCheck_2595_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2588_);
                            lean_dec(v___x_2576_);
                            v___x_2590_ = lean_box(0);
                            v_isShared_2591_ = v_isSharedCheck_2595_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_exprArgs_2568_);
                    lean_del_object(v___x_2552_);
                    v_a_2596_ = lean_ctor_get(v___x_2572_, 0);
                    v_isSharedCheck_2603_ = (!lean_is_exclusive(v___x_2572_)) as u8;
                    if v_isSharedCheck_2603_ == 0 {
                        v___x_2598_ = v___x_2572_;
                        v_isShared_2599_ = v_isSharedCheck_2603_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2596_);
                        lean_dec(v___x_2572_);
                        v___x_2598_ = lean_box(0);
                        v_isShared_2599_ = v_isSharedCheck_2603_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2553_ == 0 {
                    lean_ctor_set(v___x_2552_, 1, v_a_2577_);
                    lean_ctor_set(v___x_2552_, 0, v_a_2573_);
                    v___x_2582_ = v___x_2552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_a_2573_);
                    lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_a_2577_);
                    v___x_2582_ = v_reuseFailAlloc_2586_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2580_ == 0 {
                    lean_ctor_set(v___x_2579_, 0, v___x_2582_);
                    v___x_2584_ = v___x_2579_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
                    v___x_2584_ = v_reuseFailAlloc_2585_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2584_;
            }
            6 => {
                if v_isShared_2591_ == 0 {
                    v___x_2593_ = v___x_2590_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
                    v___x_2593_ = v_reuseFailAlloc_2594_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2593_;
            }
            8 => {
                if v_isShared_2599_ == 0 {
                    v___x_2601_ = v___x_2598_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
                    v___x_2601_ = v_reuseFailAlloc_2602_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2601_;
            }
            10 => {
                if v_isShared_2613_ == 0 {
                    v___x_2615_ = v___x_2612_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
                    v___x_2615_ = v_reuseFailAlloc_2616_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2615_;
            }
            12 => {
                if v_isShared_2621_ == 0 {
                    v___x_2623_ = v___x_2620_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2623_;
            }
            14 => {
                if v_isShared_2629_ == 0 {
                    v___x_2631_ = v___x_2628_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
                    v___x_2631_ = v_reuseFailAlloc_2632_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2631_;
            }
            16 => {
                if v_isShared_2639_ == 0 {
                    v___x_2641_ = v___x_2638_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2641_;
            }
            18 => {
                if v_isShared_2647_ == 0 {
                    v___x_2649_ = v___x_2646_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
                    v___x_2649_ = v_reuseFailAlloc_2650_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2649_;
            }
            20 => {
                if v_isShared_2655_ == 0 {
                    v___x_2657_ = v___x_2654_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
                    v___x_2657_ = v_reuseFailAlloc_2658_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2657_;
            }
            22 => {
                if v_isShared_2663_ == 0 {
                    v___x_2665_ = v___x_2662_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
                    v___x_2665_ = v_reuseFailAlloc_2666_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2665_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___boxed(
    mut v_goalType_2668_: *mut LeanObject,
    mut v___x_2669_: *mut LeanObject,
    mut v_cfg_2670_: *mut LeanObject,
    mut v___y_2671_: *mut LeanObject,
    mut v___y_2672_: *mut LeanObject,
    mut v___y_2673_: *mut LeanObject,
    mut v___y_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cfg_boxed_2676_: u8 = 0;
    let mut v_res_2677_: *mut LeanObject = core::ptr::null_mut();
    v_cfg_boxed_2676_ = (lean_unbox(v_cfg_2670_) as u8);
    v_res_2677_ =
        l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1(
            v_goalType_2668_,
            v___x_2669_,
            v_cfg_boxed_2676_,
            v___y_2671_,
            v___y_2672_,
            v___y_2673_,
            v___y_2674_,
        );
    lean_dec(v___y_2674_);
    lean_dec_ref(v___y_2673_);
    lean_dec(v___y_2672_);
    lean_dec_ref(v___y_2671_);
    return v_res_2677_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(
    mut v_mainGoal_2678_: *mut LeanObject,
    mut v_goalType_2679_: *mut LeanObject,
    mut v_cfg_2680_: u8,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
    mut v_a_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    v___x_2686_ = lean_box(0);
    v___x_2687_ = lean_box((v_cfg_2680_) as usize);
    v___f_2688_ = lean_alloc_closure(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___lam__1___boxed as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___f_2688_, 0, v_goalType_2679_);
    lean_closure_set(v___f_2688_, 1, v___x_2686_);
    lean_closure_set(v___f_2688_, 2, v___x_2687_);
    v___x_2689_ = l_Lean_MVarId_withContext___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType_spec__3___redArg(v_mainGoal_2678_, v___f_2688_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
    return v___x_2689_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType___boxed(
    mut v_mainGoal_2690_: *mut LeanObject,
    mut v_goalType_2691_: *mut LeanObject,
    mut v_cfg_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
    mut v_a_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cfg_boxed_2698_: u8 = 0;
    let mut v_res_2699_: *mut LeanObject = core::ptr::null_mut();
    v_cfg_boxed_2698_ = (lean_unbox(v_cfg_2692_) as u8);
    v_res_2699_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(
        v_mainGoal_2690_,
        v_goalType_2691_,
        v_cfg_boxed_2698_,
        v_a_2693_,
        v_a_2694_,
        v_a_2695_,
        v_a_2696_,
    );
    lean_dec(v_a_2696_);
    lean_dec_ref(v_a_2695_);
    lean_dec(v_a_2694_);
    lean_dec_ref(v_a_2693_);
    return v_res_2699_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    v___x_2700_ = lean_box(0);
    v___x_2701_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_2702_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2702_, 0, v___x_2701_);
    lean_ctor_set(v___x_2702_, 1, v___x_2700_);
    return v___x_2702_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    v___x_2704_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___closed__0);
    v___x_2705_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2705_, 0, v___x_2704_);
    return v___x_2705_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg___boxed(
    mut v___y_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2707_: *mut LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
    return v_res_2707_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0(
    mut v_00_u03b1_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
    mut v___y_2710_: *mut LeanObject,
    mut v___y_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___x_2714_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
    return v___x_2714_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___boxed(
    mut v_00_u03b1_2715_: *mut LeanObject,
    mut v___y_2716_: *mut LeanObject,
    mut v___y_2717_: *mut LeanObject,
    mut v___y_2718_: *mut LeanObject,
    mut v___y_2719_: *mut LeanObject,
    mut v___y_2720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2721_: *mut LeanObject = core::ptr::null_mut();
    v_res_2721_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0(v_00_u03b1_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
    lean_dec(v___y_2719_);
    lean_dec_ref(v___y_2718_);
    lean_dec(v___y_2717_);
    lean_dec_ref(v___y_2716_);
    return v_res_2721_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(
    mut v_msgData_2722_: *mut LeanObject,
    mut v___y_2723_: *mut LeanObject,
    mut v___y_2724_: *mut LeanObject,
    mut v___y_2725_: *mut LeanObject,
    mut v___y_2726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    v___x_2728_ = lean_st_ref_get(v___y_2726_);
    v_env_2729_ = lean_ctor_get(v___x_2728_, 0);
    lean_inc_ref(v_env_2729_);
    lean_dec(v___x_2728_);
    v___x_2730_ = lean_st_ref_get(v___y_2724_);
    v_mctx_2731_ = lean_ctor_get(v___x_2730_, 0);
    lean_inc_ref(v_mctx_2731_);
    lean_dec(v___x_2730_);
    v_lctx_2732_ = lean_ctor_get(v___y_2723_, 2);
    v_options_2733_ = lean_ctor_get(v___y_2725_, 2);
    lean_inc_ref(v_options_2733_);
    lean_inc_ref(v_lctx_2732_);
    v___x_2734_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2734_, 0, v_env_2729_);
    lean_ctor_set(v___x_2734_, 1, v_mctx_2731_);
    lean_ctor_set(v___x_2734_, 2, v_lctx_2732_);
    lean_ctor_set(v___x_2734_, 3, v_options_2733_);
    v___x_2735_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2735_, 0, v___x_2734_);
    lean_ctor_set(v___x_2735_, 1, v_msgData_2722_);
    v___x_2736_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2736_, 0, v___x_2735_);
    return v___x_2736_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1___boxed(
    mut v_msgData_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2743_: *mut LeanObject = core::ptr::null_mut();
    v_res_2743_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msgData_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
    lean_dec(v___y_2741_);
    lean_dec_ref(v___y_2740_);
    lean_dec(v___y_2739_);
    lean_dec_ref(v___y_2738_);
    return v_res_2743_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(
    mut v_msg_2744_: *mut LeanObject,
    mut v___y_2745_: *mut LeanObject,
    mut v___y_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
    mut v___y_2748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2755_: u8 = 0;
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2750_ = lean_ctor_get(v___y_2747_, 5);
                v___x_2751_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_);
                v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
                v_isSharedCheck_2760_ = (!lean_is_exclusive(v___x_2751_)) as u8;
                if v_isSharedCheck_2760_ == 0 {
                    v___x_2754_ = v___x_2751_;
                    v_isShared_2755_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2752_);
                    lean_dec(v___x_2751_);
                    v___x_2754_ = lean_box(0);
                    v_isShared_2755_ = v_isSharedCheck_2760_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2750_);
                v___x_2756_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2756_, 0, v_ref_2750_);
                lean_ctor_set(v___x_2756_, 1, v_a_2752_);
                if v_isShared_2755_ == 0 {
                    lean_ctor_set_tag(v___x_2754_, 1);
                    lean_ctor_set(v___x_2754_, 0, v___x_2756_);
                    v___x_2758_ = v___x_2754_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
                    v___x_2758_ = v_reuseFailAlloc_2759_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg___boxed(
    mut v_msg_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
    mut v___y_2765_: *mut LeanObject,
    mut v___y_2766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2767_: *mut LeanObject = core::ptr::null_mut();
    v_res_2767_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v_msg_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
    lean_dec(v___y_2765_);
    lean_dec_ref(v___y_2764_);
    lean_dec(v___y_2763_);
    lean_dec_ref(v___y_2762_);
    return v_res_2767_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    v___x_2770_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__1;
    v___x_2771_ = l_Lean_stringToMessageData(v___x_2770_);
    return v___x_2771_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(
    mut v_ctor_2772_: *mut LeanObject,
    mut v_args_2773_: *mut LeanObject,
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v_a_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: u8 = 0;
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2815_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2800_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__0;
                v___x_2801_ = lean_string_dec_eq(v_ctor_2772_, v___x_2800_);
                if v___x_2801_ == 0 {
                    v___x_2802_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__0___redArg();
                    return v___x_2802_;
                } else {
                    v___x_2803_ = lean_array_get_size(v_args_2773_);
                    v___x_2804_ = lean_unsigned_to_nat(1);
                    v___x_2805_ = lean_nat_dec_eq(v___x_2803_, v___x_2804_);
                    if v___x_2805_ == 0 {
                        v___x_2806_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___closed__2);
                        v___x_2807_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v___x_2806_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
                        v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
                        v_isSharedCheck_2815_ = (!lean_is_exclusive(v___x_2807_)) as u8;
                        if v_isSharedCheck_2815_ == 0 {
                            v___x_2810_ = v___x_2807_;
                            v_isShared_2811_ = v_isSharedCheck_2815_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2808_);
                            lean_dec(v___x_2807_);
                            v___x_2810_ = lean_box(0);
                            v_isShared_2811_ = v_isSharedCheck_2815_;
                            state = 6;
                            continue;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2780_ = l_Lean_instInhabitedExpr;
                v___x_2781_ = lean_unsigned_to_nat(0);
                v___x_2782_ = lean_array_get_borrowed(v___x_2780_, v_args_2773_, v___x_2781_);
                lean_inc(v___x_2782_);
                v___x_2783_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                    v___x_2782_,
                    v___y_2774_,
                    v___y_2775_,
                    v___y_2776_,
                    v___y_2777_,
                );
                if lean_obj_tag(v___x_2783_) == 0 {
                    v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2791_ = (!lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2791_ == 0 {
                        v___x_2786_ = v___x_2783_;
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2784_);
                        lean_dec(v___x_2783_);
                        v___x_2786_ = lean_box(0);
                        v_isShared_2787_ = v_isSharedCheck_2791_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2792_ = lean_ctor_get(v___x_2783_, 0);
                    v_isSharedCheck_2799_ = (!lean_is_exclusive(v___x_2783_)) as u8;
                    if v_isSharedCheck_2799_ == 0 {
                        v___x_2794_ = v___x_2783_;
                        v_isShared_2795_ = v_isSharedCheck_2799_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2792_);
                        lean_dec(v___x_2783_);
                        v___x_2794_ = lean_box(0);
                        v_isShared_2795_ = v_isSharedCheck_2799_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2787_ == 0 {
                    v___x_2789_ = v___x_2786_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2789_;
            }
            4 => {
                if v_isShared_2795_ == 0 {
                    v___x_2797_ = v___x_2794_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
                    v___x_2797_ = v_reuseFailAlloc_2798_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2797_;
            }
            6 => {
                if v_isShared_2811_ == 0 {
                    v___x_2813_ = v___x_2810_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
                    v___x_2813_ = v_reuseFailAlloc_2814_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2813_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0___boxed(
    mut v_ctor_2816_: *mut LeanObject,
    mut v_args_2817_: *mut LeanObject,
    mut v___y_2818_: *mut LeanObject,
    mut v___y_2819_: *mut LeanObject,
    mut v___y_2820_: *mut LeanObject,
    mut v___y_2821_: *mut LeanObject,
    mut v___y_2822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2823_: *mut LeanObject = core::ptr::null_mut();
    v_res_2823_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___lam__0(v_ctor_2816_, v_args_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
    lean_dec(v___y_2821_);
    lean_dec_ref(v___y_2820_);
    lean_dec(v___y_2819_);
    lean_dec_ref(v___y_2818_);
    lean_dec_ref(v_args_2817_);
    lean_dec_ref(v_ctor_2816_);
    return v_res_2823_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(
    mut v_a_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
    mut v_a_2836_: *mut LeanObject,
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    v___f_2840_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__0;
    v___x_2841_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5;
    v___x_2842_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_2841_,
        v___f_2840_,
        v_a_2834_,
        v_a_2835_,
        v_a_2836_,
        v_a_2837_,
        v_a_2838_,
    );
    return v___x_2842_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___boxed(
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_a_2845_: *mut LeanObject,
    mut v_a_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
    mut v_a_2848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2849_: *mut LeanObject = core::ptr::null_mut();
    v_res_2849_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_);
    lean_dec(v_a_2847_);
    lean_dec_ref(v_a_2846_);
    lean_dec(v_a_2845_);
    lean_dec_ref(v_a_2844_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(
    mut v_00_u03b1_2850_: *mut LeanObject,
    mut v_msg_2851_: *mut LeanObject,
    mut v___y_2852_: *mut LeanObject,
    mut v___y_2853_: *mut LeanObject,
    mut v___y_2854_: *mut LeanObject,
    mut v___y_2855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    v___x_2857_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___redArg(v_msg_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_);
    return v___x_2857_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1___boxed(
    mut v_00_u03b1_2858_: *mut LeanObject,
    mut v_msg_2859_: *mut LeanObject,
    mut v___y_2860_: *mut LeanObject,
    mut v___y_2861_: *mut LeanObject,
    mut v___y_2862_: *mut LeanObject,
    mut v___y_2863_: *mut LeanObject,
    mut v___y_2864_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2865_: *mut LeanObject = core::ptr::null_mut();
    v_res_2865_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1(v_00_u03b1_2858_, v_msg_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
    lean_dec(v___y_2863_);
    lean_dec_ref(v___y_2862_);
    lean_dec(v___y_2861_);
    lean_dec_ref(v___y_2860_);
    return v_res_2865_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1()
-> *mut LeanObject {
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    v___x_2867_ = lean_box(0);
    v___x_2868_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5;
    v___x_2869_ = l_Lean_Expr_const___override(v___x_2868_, v___x_2867_);
    return v___x_2869_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2()
-> *mut LeanObject {
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    v___x_2870_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1);
    v___x_2871_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2871_, 0, v___x_2870_);
    return v___x_2871_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3()
-> *mut LeanObject {
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    v___x_2872_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2);
    v___x_2873_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__0;
    v___x_2874_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2874_, 0, v___x_2873_);
    lean_ctor_set(v___x_2874_, 1, v___x_2872_);
    return v___x_2874_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig()
-> *mut LeanObject {
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    v___x_2875_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3_once), _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__3);
    return v___x_2875_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    v___x_2876_ = lean_box(1);
    v___x_2877_ = l_Lean_MessageData_ofFormat(v___x_2876_);
    return v___x_2877_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    v___x_2881_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2;
    v___x_2882_ = l_Lean_MessageData_ofFormat(v___x_2881_);
    return v___x_2882_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(
    mut v_x_2883_: *mut LeanObject,
    mut v_x_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v_before_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2906_: u8 = 0;
    let mut v_unused_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2884_) == 0 {
                    return v_x_2883_;
                } else {
                    v_head_2885_ = lean_ctor_get(v_x_2884_, 0);
                    v_tail_2886_ = lean_ctor_get(v_x_2884_, 1);
                    v_isSharedCheck_2908_ = (!lean_is_exclusive(v_x_2884_)) as u8;
                    if v_isSharedCheck_2908_ == 0 {
                        v___x_2888_ = v_x_2884_;
                        v_isShared_2889_ = v_isSharedCheck_2908_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2886_);
                        lean_inc(v_head_2885_);
                        lean_dec(v_x_2884_);
                        v___x_2888_ = lean_box(0);
                        v_isShared_2889_ = v_isSharedCheck_2908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2890_ = lean_ctor_get(v_head_2885_, 0);
                v_isSharedCheck_2906_ = (!lean_is_exclusive(v_head_2885_)) as u8;
                if v_isSharedCheck_2906_ == 0 {
                    v_unused_2907_ = lean_ctor_get(v_head_2885_, 1);
                    lean_dec(v_unused_2907_);
                    v___x_2892_ = v_head_2885_;
                    v_isShared_2893_ = v_isSharedCheck_2906_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_2890_);
                    lean_dec(v_head_2885_);
                    v___x_2892_ = lean_box(0);
                    v_isShared_2893_ = v_isSharedCheck_2906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2894_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_2893_ == 0 {
                    lean_ctor_set_tag(v___x_2892_, 7);
                    lean_ctor_set(v___x_2892_, 1, v___x_2894_);
                    lean_ctor_set(v___x_2892_, 0, v_x_2883_);
                    v___x_2896_ = v___x_2892_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2905_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 0, v_x_2883_);
                    lean_ctor_set(v_reuseFailAlloc_2905_, 1, v___x_2894_);
                    v___x_2896_ = v_reuseFailAlloc_2905_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2897_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
                if v_isShared_2889_ == 0 {
                    lean_ctor_set_tag(v___x_2888_, 7);
                    lean_ctor_set(v___x_2888_, 1, v___x_2897_);
                    lean_ctor_set(v___x_2888_, 0, v___x_2896_);
                    v___x_2899_ = v___x_2888_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2904_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2904_, 1, v___x_2897_);
                    v___x_2899_ = v_reuseFailAlloc_2904_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2900_ = l_Lean_MessageData_ofSyntax(v_before_2890_);
                v___x_2901_ = l_Lean_indentD(v___x_2900_);
                v___x_2902_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2902_, 0, v___x_2899_);
                lean_ctor_set(v___x_2902_, 1, v___x_2901_);
                v_x_2883_ = v___x_2902_;
                v_x_2884_ = v_tail_2886_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(
    mut v_opts_2909_: *mut LeanObject,
    mut v_opt_2910_: *mut LeanObject,
) -> u8 {
    let mut v_name_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    v_name_2911_ = lean_ctor_get(v_opt_2910_, 0);
    v_defValue_2912_ = lean_ctor_get(v_opt_2910_, 1);
    v_map_2913_ = lean_ctor_get(v_opts_2909_, 0);
    v___x_2914_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2913_,
            v_name_2911_,
        );
    if lean_obj_tag(v___x_2914_) == 0 {
        let mut v___x_2915_: u8 = 0;
        v___x_2915_ = (lean_unbox(v_defValue_2912_) as u8);
        return v___x_2915_;
    } else {
        let mut v_val_2916_: *mut LeanObject = core::ptr::null_mut();
        v_val_2916_ = lean_ctor_get(v___x_2914_, 0);
        lean_inc(v_val_2916_);
        lean_dec_ref_known(v___x_2914_, 1);
        if lean_obj_tag(v_val_2916_) == 1 {
            let mut v_v_2917_: u8 = 0;
            v_v_2917_ = lean_ctor_get_uint8(v_val_2916_, 0 as u32);
            lean_dec_ref_known(v_val_2916_, 0);
            return v_v_2917_;
        } else {
            let mut v___x_2918_: u8 = 0;
            lean_dec(v_val_2916_);
            v___x_2918_ = (lean_unbox(v_defValue_2912_) as u8);
            return v___x_2918_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_opts_2919_: *mut LeanObject,
    mut v_opt_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2921_: u8 = 0;
    let mut v_r_2922_: *mut LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_2919_, v_opt_2920_);
    lean_dec_ref(v_opt_2920_);
    lean_dec_ref(v_opts_2919_);
    v_r_2922_ = lean_box((v_res_2921_) as usize);
    return v_r_2922_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    v___x_2926_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1;
    v___x_2927_ = l_Lean_MessageData_ofFormat(v___x_2926_);
    return v___x_2927_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(
    mut v_msgData_2928_: *mut LeanObject,
    mut v_macroStack_2929_: *mut LeanObject,
    mut v___y_2930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: u8 = 0;
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2941_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2953_: u8 = 0;
    let mut v_unused_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2932_ = lean_ctor_get(v___y_2930_, 2);
                v___x_2933_ = l_Lean_Elab_pp_macroStack;
                v___x_2934_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_2932_, v___x_2933_);
                if v___x_2934_ == 0 {
                    lean_dec(v_macroStack_2929_);
                    v___x_2935_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2935_, 0, v_msgData_2928_);
                    return v___x_2935_;
                } else {
                    if lean_obj_tag(v_macroStack_2929_) == 0 {
                        v___x_2936_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2936_, 0, v_msgData_2928_);
                        return v___x_2936_;
                    } else {
                        v_head_2937_ = lean_ctor_get(v_macroStack_2929_, 0);
                        lean_inc(v_head_2937_);
                        v_after_2938_ = lean_ctor_get(v_head_2937_, 1);
                        v_isSharedCheck_2953_ = (!lean_is_exclusive(v_head_2937_)) as u8;
                        if v_isSharedCheck_2953_ == 0 {
                            v_unused_2954_ = lean_ctor_get(v_head_2937_, 0);
                            lean_dec(v_unused_2954_);
                            v___x_2940_ = v_head_2937_;
                            v_isShared_2941_ = v_isSharedCheck_2953_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_2938_);
                            lean_dec(v_head_2937_);
                            v___x_2940_ = lean_box(0);
                            v_isShared_2941_ = v_isSharedCheck_2953_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2942_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_2941_ == 0 {
                    lean_ctor_set_tag(v___x_2940_, 7);
                    lean_ctor_set(v___x_2940_, 1, v___x_2942_);
                    lean_ctor_set(v___x_2940_, 0, v_msgData_2928_);
                    v___x_2944_ = v___x_2940_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2952_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_msgData_2928_);
                    lean_ctor_set(v_reuseFailAlloc_2952_, 1, v___x_2942_);
                    v___x_2944_ = v_reuseFailAlloc_2952_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2945_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
                v___x_2946_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2946_, 0, v___x_2944_);
                lean_ctor_set(v___x_2946_, 1, v___x_2945_);
                v___x_2947_ = l_Lean_MessageData_ofSyntax(v_after_2938_);
                v___x_2948_ = l_Lean_indentD(v___x_2947_);
                v_msgData_2949_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_2949_, 0, v___x_2946_);
                lean_ctor_set(v_msgData_2949_, 1, v___x_2948_);
                v___x_2950_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_2949_, v_macroStack_2929_);
                v___x_2951_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2951_, 0, v___x_2950_);
                return v___x_2951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_msgData_2955_: *mut LeanObject,
    mut v_macroStack_2956_: *mut LeanObject,
    mut v___y_2957_: *mut LeanObject,
    mut v___y_2958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2959_: *mut LeanObject = core::ptr::null_mut();
    v_res_2959_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_2955_, v_macroStack_2956_, v___y_2957_);
    lean_dec_ref(v___y_2957_);
    return v_res_2959_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(
    mut v_msg_2960_: *mut LeanObject,
    mut v___y_2961_: *mut LeanObject,
    mut v___y_2962_: *mut LeanObject,
    mut v___y_2963_: *mut LeanObject,
    mut v___y_2964_: *mut LeanObject,
    mut v___y_2965_: *mut LeanObject,
    mut v___y_2966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2977_: u8 = 0;
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2968_ = lean_ctor_get(v___y_2965_, 5);
                v___x_2969_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_2960_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
                v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
                lean_inc(v_a_2970_);
                lean_dec_ref(v___x_2969_);
                v_macroStack_2971_ = lean_ctor_get(v___y_2961_, 1);
                v___x_2972_ = l_Lean_Elab_getBetterRef(v_ref_2968_, v_macroStack_2971_);
                lean_inc(v_macroStack_2971_);
                v___x_2973_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_2970_, v_macroStack_2971_, v___y_2965_);
                v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
                v_isSharedCheck_2982_ = (!lean_is_exclusive(v___x_2973_)) as u8;
                if v_isSharedCheck_2982_ == 0 {
                    v___x_2976_ = v___x_2973_;
                    v_isShared_2977_ = v_isSharedCheck_2982_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2974_);
                    lean_dec(v___x_2973_);
                    v___x_2976_ = lean_box(0);
                    v_isShared_2977_ = v_isSharedCheck_2982_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2978_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2978_, 0, v___x_2972_);
                lean_ctor_set(v___x_2978_, 1, v_a_2974_);
                if v_isShared_2977_ == 0 {
                    lean_ctor_set_tag(v___x_2976_, 1);
                    lean_ctor_set(v___x_2976_, 0, v___x_2978_);
                    v___x_2980_ = v___x_2976_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(
    mut v_msg_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2991_: *mut LeanObject = core::ptr::null_mut();
    v_res_2991_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
    lean_dec(v___y_2989_);
    lean_dec_ref(v___y_2988_);
    lean_dec(v___y_2987_);
    lean_dec_ref(v___y_2986_);
    lean_dec(v___y_2985_);
    lean_dec_ref(v___y_2984_);
    return v_res_2991_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    v___x_2992_ = lean_box(0);
    v___x_2993_ = l_Lean_Elab_abortTermExceptionId;
    v___x_2994_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2994_, 0, v___x_2993_);
    lean_ctor_set(v___x_2994_, 1, v___x_2992_);
    return v___x_2994_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg()
-> *mut LeanObject {
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    v___x_2996_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
    v___x_2997_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2997_, 0, v___x_2996_);
    return v___x_2997_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(
    mut v___y_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v_res_2999_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(
    mut v_e_3000_: *mut LeanObject,
    mut v___y_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3003_: u8 = 0;
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_unused_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3003_ = l_Lean_Expr_hasMVar(v_e_3000_);
                if v___x_3003_ == 0 {
                    v___x_3004_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3004_, 0, v_e_3000_);
                    return v___x_3004_;
                } else {
                    v___x_3005_ = lean_st_ref_get(v___y_3001_);
                    v_mctx_3006_ = lean_ctor_get(v___x_3005_, 0);
                    lean_inc_ref(v_mctx_3006_);
                    lean_dec(v___x_3005_);
                    v___x_3007_ = l_Lean_instantiateMVarsCore(v_mctx_3006_, v_e_3000_);
                    v_fst_3008_ = lean_ctor_get(v___x_3007_, 0);
                    lean_inc(v_fst_3008_);
                    v_snd_3009_ = lean_ctor_get(v___x_3007_, 1);
                    lean_inc(v_snd_3009_);
                    lean_dec_ref(v___x_3007_);
                    v___x_3010_ = lean_st_ref_take(v___y_3001_);
                    v_cache_3011_ = lean_ctor_get(v___x_3010_, 1);
                    v_zetaDeltaFVarIds_3012_ = lean_ctor_get(v___x_3010_, 2);
                    v_postponed_3013_ = lean_ctor_get(v___x_3010_, 3);
                    v_diag_3014_ = lean_ctor_get(v___x_3010_, 4);
                    v_isSharedCheck_3023_ = (!lean_is_exclusive(v___x_3010_)) as u8;
                    if v_isSharedCheck_3023_ == 0 {
                        v_unused_3024_ = lean_ctor_get(v___x_3010_, 0);
                        lean_dec(v_unused_3024_);
                        v___x_3016_ = v___x_3010_;
                        v_isShared_3017_ = v_isSharedCheck_3023_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3014_);
                        lean_inc(v_postponed_3013_);
                        lean_inc(v_zetaDeltaFVarIds_3012_);
                        lean_inc(v_cache_3011_);
                        lean_dec(v___x_3010_);
                        v___x_3016_ = lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3023_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3017_ == 0 {
                    lean_ctor_set(v___x_3016_, 0, v_snd_3009_);
                    v___x_3019_ = v___x_3016_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_snd_3009_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_cache_3011_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_zetaDeltaFVarIds_3012_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_postponed_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_diag_3014_);
                    v___x_3019_ = v_reuseFailAlloc_3022_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3020_ = lean_st_ref_set(v___y_3001_, v___x_3019_);
                v___x_3021_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3021_, 0, v_fst_3008_);
                return v___x_3021_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(
    mut v_e_3025_: *mut LeanObject,
    mut v___y_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3028_: *mut LeanObject = core::ptr::null_mut();
    v_res_3028_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3025_, v___y_3026_);
    lean_dec(v___y_3026_);
    return v_res_3028_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    v___x_3030_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__0;
    v___x_3031_ = l_Lean_stringToMessageData(v___x_3030_);
    return v___x_3031_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    v___x_3032_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__1);
    v___x_3033_ = l_Lean_MessageData_ofExpr(v___x_3032_);
    return v___x_3033_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    v___x_3034_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__2);
    v___x_3035_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__1);
    v___x_3036_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3036_, 0, v___x_3035_);
    lean_ctor_set(v___x_3036_, 1, v___x_3034_);
    return v___x_3036_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    v___x_3038_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__4;
    v___x_3039_ = l_Lean_stringToMessageData(v___x_3038_);
    return v___x_3039_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    v___x_3040_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__5);
    v___x_3041_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__3);
    v___x_3042_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3042_, 0, v___x_3041_);
    lean_ctor_set(v___x_3042_, 1, v___x_3040_);
    return v___x_3042_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8()
-> *mut LeanObject {
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut LeanObject = core::ptr::null_mut();
    v___x_3044_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__7;
    v___x_3045_ = l_Lean_stringToMessageData(v___x_3044_);
    return v___x_3045_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10()
-> *mut LeanObject {
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    v___x_3047_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__9;
    v___x_3048_ = l_Lean_stringToMessageData(v___x_3047_);
    return v___x_3048_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(
    mut v_stx_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
    mut v_a_3052_: *mut LeanObject,
    mut v_a_3053_: *mut LeanObject,
    mut v_a_3054_: *mut LeanObject,
    mut v_a_3055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: u8 = 0;
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3075_: u8 = 0;
    let mut v_cancelTk_x3f_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3077_: u8 = 0;
    let mut v_inheritedTraceOptions_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: u8 = 0;
    let mut v_ref_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3096_: u8 = 0;
    let mut v_id_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3100_: u8 = 0;
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3110_: u8 = 0;
    let mut v_unused_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: u8 = 0;
    let mut v___x_3123_: u8 = 0;
    let mut v___y_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: u8 = 0;
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3140_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_a_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3152_: u8 = 0;
    let mut v_a_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3156_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut v___y_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3175_: u8 = 0;
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v___x_3180_: u8 = 0;
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut v_a_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3194_: u8 = 0;
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_3057_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig___closed__2);
                v___x_3058_ = 1;
                v___x_3059_ = lean_box(0);
                v___x_3060_ = lean_box((v___x_3058_) as usize);
                v___x_3061_ = lean_box((v___x_3058_) as usize);
                lean_inc(v_stx_3049_);
                v___x_3062_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_3062_, 0, v_stx_3049_);
                lean_closure_set(v___x_3062_, 1, v_ty_x3f_3057_);
                lean_closure_set(v___x_3062_, 2, v___x_3060_);
                lean_closure_set(v___x_3062_, 3, v___x_3061_);
                lean_closure_set(v___x_3062_, 4, v___x_3059_);
                v_fileName_3063_ = lean_ctor_get(v_a_3054_, 0);
                v_fileMap_3064_ = lean_ctor_get(v_a_3054_, 1);
                v_options_3065_ = lean_ctor_get(v_a_3054_, 2);
                v_currRecDepth_3066_ = lean_ctor_get(v_a_3054_, 3);
                v_maxRecDepth_3067_ = lean_ctor_get(v_a_3054_, 4);
                v_ref_3068_ = lean_ctor_get(v_a_3054_, 5);
                v_currNamespace_3069_ = lean_ctor_get(v_a_3054_, 6);
                v_openDecls_3070_ = lean_ctor_get(v_a_3054_, 7);
                v_initHeartbeats_3071_ = lean_ctor_get(v_a_3054_, 8);
                v_maxHeartbeats_3072_ = lean_ctor_get(v_a_3054_, 9);
                v_quotContext_3073_ = lean_ctor_get(v_a_3054_, 10);
                v_currMacroScope_3074_ = lean_ctor_get(v_a_3054_, 11);
                v_diag_3075_ = lean_ctor_get_uint8(
                    v_a_3054_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3076_ = lean_ctor_get(v_a_3054_, 12);
                v_suppressElabErrors_3077_ = lean_ctor_get_uint8(
                    v_a_3054_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3078_ = lean_ctor_get(v_a_3054_, 13);
                v___x_3079_ = 1;
                v_ref_3080_ = l_Lean_replaceRef(v_stx_3049_, v_ref_3068_);
                lean_dec(v_stx_3049_);
                lean_inc_ref(v_inheritedTraceOptions_3078_);
                lean_inc(v_cancelTk_x3f_3076_);
                lean_inc(v_currMacroScope_3074_);
                lean_inc(v_quotContext_3073_);
                lean_inc(v_maxHeartbeats_3072_);
                lean_inc(v_initHeartbeats_3071_);
                lean_inc(v_openDecls_3070_);
                lean_inc(v_currNamespace_3069_);
                lean_inc(v_maxRecDepth_3067_);
                lean_inc(v_currRecDepth_3066_);
                lean_inc_ref(v_options_3065_);
                lean_inc_ref(v_fileMap_3064_);
                lean_inc_ref(v_fileName_3063_);
                v___x_3081_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3081_, 0, v_fileName_3063_);
                lean_ctor_set(v___x_3081_, 1, v_fileMap_3064_);
                lean_ctor_set(v___x_3081_, 2, v_options_3065_);
                lean_ctor_set(v___x_3081_, 3, v_currRecDepth_3066_);
                lean_ctor_set(v___x_3081_, 4, v_maxRecDepth_3067_);
                lean_ctor_set(v___x_3081_, 5, v_ref_3080_);
                lean_ctor_set(v___x_3081_, 6, v_currNamespace_3069_);
                lean_ctor_set(v___x_3081_, 7, v_openDecls_3070_);
                lean_ctor_set(v___x_3081_, 8, v_initHeartbeats_3071_);
                lean_ctor_set(v___x_3081_, 9, v_maxHeartbeats_3072_);
                lean_ctor_set(v___x_3081_, 10, v_quotContext_3073_);
                lean_ctor_set(v___x_3081_, 11, v_currMacroScope_3074_);
                lean_ctor_set(v___x_3081_, 12, v_cancelTk_x3f_3076_);
                lean_ctor_set(v___x_3081_, 13, v_inheritedTraceOptions_3078_);
                lean_ctor_set_uint8(
                    v___x_3081_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_3075_,
                );
                lean_ctor_set_uint8(
                    v___x_3081_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3077_,
                );
                v___x_3082_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_3062_,
                        v___x_3079_,
                        v_a_3050_,
                        v_a_3051_,
                        v_a_3052_,
                        v_a_3053_,
                        v___x_3081_,
                        v_a_3055_,
                    );
                if lean_obj_tag(v___x_3082_) == 0 {
                    v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
                    lean_inc(v_a_3083_);
                    lean_dec_ref_known(v___x_3082_, 1);
                    v___x_3084_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_3083_, v_a_3053_);
                    v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
                    lean_inc(v_a_3085_);
                    lean_dec_ref(v___x_3084_);
                    v___x_3180_ = l_Lean_Expr_hasSorry(v_a_3085_);
                    if v___x_3180_ == 0 {
                        v___y_3125_ = v_a_3050_;
                        v___y_3126_ = v_a_3051_;
                        v___y_3127_ = v_a_3052_;
                        v___y_3128_ = v_a_3053_;
                        v___y_3129_ = v___x_3081_;
                        v___y_3130_ = v_a_3055_;
                        state = 5;
                        continue;
                    } else {
                        v___x_3181_ = l_Lean_Expr_hasSyntheticSorry(v_a_3085_);
                        if v___x_3181_ == 0 {
                            v___y_3162_ = v_a_3050_;
                            v___y_3163_ = v_a_3051_;
                            v___y_3164_ = v_a_3052_;
                            v___y_3165_ = v_a_3053_;
                            v___y_3166_ = v___x_3081_;
                            v___y_3167_ = v_a_3055_;
                            state = 12;
                            continue;
                        } else {
                            lean_dec(v_a_3085_);
                            lean_dec_ref_known(v___x_3081_, 14);
                            v___x_3182_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
                            v_isSharedCheck_3190_ = (!lean_is_exclusive(v___x_3182_)) as u8;
                            if v_isSharedCheck_3190_ == 0 {
                                v___x_3185_ = v___x_3182_;
                                v_isShared_3186_ = v_isSharedCheck_3190_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_3183_);
                                lean_dec(v___x_3182_);
                                v___x_3185_ = lean_box(0);
                                v_isShared_3186_ = v_isSharedCheck_3190_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_3081_, 14);
                    v_a_3191_ = lean_ctor_get(v___x_3082_, 0);
                    v_isSharedCheck_3198_ = (!lean_is_exclusive(v___x_3082_)) as u8;
                    if v_isSharedCheck_3198_ == 0 {
                        v___x_3193_ = v___x_3082_;
                        v_isShared_3194_ = v_isSharedCheck_3198_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3191_);
                        lean_dec(v___x_3082_);
                        v___x_3193_ = lean_box(0);
                        v_isShared_3194_ = v_isSharedCheck_3198_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3096_ == 0 {
                    if lean_obj_tag(v___y_3089_) == 0 {
                        lean_dec_ref_known(v___y_3089_, 2);
                        lean_dec_ref(v___y_3092_);
                        lean_dec(v_a_3085_);
                        return v___y_3093_;
                    } else {
                        v_id_3097_ = lean_ctor_get(v___y_3089_, 0);
                        v_isSharedCheck_3110_ = (!lean_is_exclusive(v___y_3089_)) as u8;
                        if v_isSharedCheck_3110_ == 0 {
                            v_unused_3111_ = lean_ctor_get(v___y_3089_, 1);
                            lean_dec(v_unused_3111_);
                            v___x_3099_ = v___y_3089_;
                            v_isShared_3100_ = v_isSharedCheck_3110_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_3097_);
                            lean_dec(v___y_3089_);
                            v___x_3099_ = lean_box(0);
                            v_isShared_3100_ = v_isSharedCheck_3110_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3092_);
                    lean_dec_ref(v___y_3089_);
                    lean_dec(v_a_3085_);
                    return v___y_3093_;
                }
            }
            2 => {
                v___x_3101_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3087_, v_id_3097_);
                lean_dec(v_id_3097_);
                if v___x_3101_ == 0 {
                    lean_del_object(v___x_3099_);
                    lean_dec_ref(v___y_3092_);
                    lean_dec(v_a_3085_);
                    return v___y_3093_;
                } else {
                    lean_dec_ref(v___y_3093_);
                    v___x_3102_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__6);
                    v___x_3103_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__8);
                    v___x_3104_ = l_Lean_indentExpr(v_a_3085_);
                    if v_isShared_3100_ == 0 {
                        lean_ctor_set_tag(v___x_3099_, 7);
                        lean_ctor_set(v___x_3099_, 1, v___x_3104_);
                        lean_ctor_set(v___x_3099_, 0, v___x_3103_);
                        v___x_3106_ = v___x_3099_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3109_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3109_, 0, v___x_3103_);
                        lean_ctor_set(v_reuseFailAlloc_3109_, 1, v___x_3104_);
                        v___x_3106_ = v_reuseFailAlloc_3109_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3107_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3107_, 0, v___x_3106_);
                lean_ctor_set(v___x_3107_, 1, v___x_3102_);
                v___x_3108_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3107_, v___y_3091_, v___y_3095_, v___y_3094_, v___y_3090_, v___y_3092_, v___y_3088_);
                lean_dec_ref(v___y_3092_);
                return v___x_3108_;
            }
            4 => {
                lean_inc(v_a_3085_);
                v___x_3119_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr(v_a_3085_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_);
                if lean_obj_tag(v___x_3119_) == 0 {
                    lean_dec_ref(v___y_3117_);
                    lean_dec(v_a_3085_);
                    return v___x_3119_;
                } else {
                    v_a_3120_ = lean_ctor_get(v___x_3119_, 0);
                    lean_inc(v_a_3120_);
                    v___x_3121_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_3122_ = l_Lean_Exception_isInterrupt(v_a_3120_);
                    if v___x_3122_ == 0 {
                        lean_inc(v_a_3120_);
                        v___x_3123_ = l_Lean_Exception_isRuntime(v_a_3120_);
                        v___y_3087_ = v___x_3121_;
                        v___y_3088_ = v___y_3118_;
                        v___y_3089_ = v_a_3120_;
                        v___y_3090_ = v___y_3116_;
                        v___y_3091_ = v___y_3113_;
                        v___y_3092_ = v___y_3117_;
                        v___y_3093_ = v___x_3119_;
                        v___y_3094_ = v___y_3115_;
                        v___y_3095_ = v___y_3114_;
                        v___y_3096_ = v___x_3123_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3087_ = v___x_3121_;
                        v___y_3088_ = v___y_3118_;
                        v___y_3089_ = v_a_3120_;
                        v___y_3090_ = v___y_3116_;
                        v___y_3091_ = v___y_3113_;
                        v___y_3092_ = v___y_3117_;
                        v___y_3093_ = v___x_3119_;
                        v___y_3094_ = v___y_3115_;
                        v___y_3095_ = v___y_3114_;
                        v___y_3096_ = v___x_3122_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                lean_inc(v_a_3085_);
                v___x_3131_ = l_Lean_Meta_getMVars(
                    v_a_3085_,
                    v___y_3127_,
                    v___y_3128_,
                    v___y_3129_,
                    v___y_3130_,
                );
                if lean_obj_tag(v___x_3131_) == 0 {
                    v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
                    lean_inc(v_a_3132_);
                    lean_dec_ref_known(v___x_3131_, 1);
                    v___x_3133_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_3132_,
                        v___x_3059_,
                        v___y_3125_,
                        v___y_3126_,
                        v___y_3127_,
                        v___y_3128_,
                        v___y_3129_,
                        v___y_3130_,
                    );
                    lean_dec(v_a_3132_);
                    if lean_obj_tag(v___x_3133_) == 0 {
                        v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
                        lean_inc(v_a_3134_);
                        lean_dec_ref_known(v___x_3133_, 1);
                        v___x_3135_ = (lean_unbox(v_a_3134_) as u8);
                        lean_dec(v_a_3134_);
                        if v___x_3135_ == 0 {
                            v___y_3113_ = v___y_3125_;
                            v___y_3114_ = v___y_3126_;
                            v___y_3115_ = v___y_3127_;
                            v___y_3116_ = v___y_3128_;
                            v___y_3117_ = v___y_3129_;
                            v___y_3118_ = v___y_3130_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec_ref(v___y_3129_);
                            lean_dec(v_a_3085_);
                            v___x_3136_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_3137_ = lean_ctor_get(v___x_3136_, 0);
                            v_isSharedCheck_3144_ = (!lean_is_exclusive(v___x_3136_)) as u8;
                            if v_isSharedCheck_3144_ == 0 {
                                v___x_3139_ = v___x_3136_;
                                v_isShared_3140_ = v_isSharedCheck_3144_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3137_);
                                lean_dec(v___x_3136_);
                                v___x_3139_ = lean_box(0);
                                v_isShared_3140_ = v_isSharedCheck_3144_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_3129_);
                        lean_dec(v_a_3085_);
                        v_a_3145_ = lean_ctor_get(v___x_3133_, 0);
                        v_isSharedCheck_3152_ = (!lean_is_exclusive(v___x_3133_)) as u8;
                        if v_isSharedCheck_3152_ == 0 {
                            v___x_3147_ = v___x_3133_;
                            v_isShared_3148_ = v_isSharedCheck_3152_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3145_);
                            lean_dec(v___x_3133_);
                            v___x_3147_ = lean_box(0);
                            v_isShared_3148_ = v_isSharedCheck_3152_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3129_);
                    lean_dec(v_a_3085_);
                    v_a_3153_ = lean_ctor_get(v___x_3131_, 0);
                    v_isSharedCheck_3160_ = (!lean_is_exclusive(v___x_3131_)) as u8;
                    if v_isSharedCheck_3160_ == 0 {
                        v___x_3155_ = v___x_3131_;
                        v_isShared_3156_ = v_isSharedCheck_3160_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3153_);
                        lean_dec(v___x_3131_);
                        v___x_3155_ = lean_box(0);
                        v_isShared_3156_ = v_isSharedCheck_3160_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3140_ == 0 {
                    v___x_3142_ = v___x_3139_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
                    v___x_3142_ = v_reuseFailAlloc_3143_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3142_;
            }
            8 => {
                if v_isShared_3148_ == 0 {
                    v___x_3150_ = v___x_3147_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
                    v___x_3150_ = v_reuseFailAlloc_3151_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3150_;
            }
            10 => {
                if v_isShared_3156_ == 0 {
                    v___x_3158_ = v___x_3155_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3153_);
                    v___x_3158_ = v_reuseFailAlloc_3159_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3158_;
            }
            12 => {
                v___x_3168_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___closed__10);
                v___x_3169_ = l_Lean_indentExpr(v_a_3085_);
                v___x_3170_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3170_, 0, v___x_3168_);
                lean_ctor_set(v___x_3170_, 1, v___x_3169_);
                v___x_3171_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3170_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
                lean_dec_ref(v___y_3166_);
                v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
                v_isSharedCheck_3179_ = (!lean_is_exclusive(v___x_3171_)) as u8;
                if v_isSharedCheck_3179_ == 0 {
                    v___x_3174_ = v___x_3171_;
                    v_isShared_3175_ = v_isSharedCheck_3179_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_3172_);
                    lean_dec(v___x_3171_);
                    v___x_3174_ = lean_box(0);
                    v_isShared_3175_ = v_isSharedCheck_3179_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3175_ == 0 {
                    v___x_3177_ = v___x_3174_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
                    v___x_3177_ = v_reuseFailAlloc_3178_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3177_;
            }
            15 => {
                if v_isShared_3186_ == 0 {
                    v___x_3188_ = v___x_3185_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3183_);
                    v___x_3188_ = v_reuseFailAlloc_3189_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3188_;
            }
            17 => {
                if v_isShared_3194_ == 0 {
                    v___x_3196_ = v___x_3193_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_a_3191_);
                    v___x_3196_ = v_reuseFailAlloc_3197_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0___boxed(
    mut v_stx_3199_: *mut LeanObject,
    mut v_a_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_a_3202_: *mut LeanObject,
    mut v_a_3203_: *mut LeanObject,
    mut v_a_3204_: *mut LeanObject,
    mut v_a_3205_: *mut LeanObject,
    mut v_a_3206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3207_: *mut LeanObject = core::ptr::null_mut();
    v_res_3207_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_stx_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_);
    lean_dec(v_a_3205_);
    lean_dec_ref(v_a_3204_);
    lean_dec(v_a_3203_);
    lean_dec_ref(v_a_3202_);
    lean_dec(v_a_3201_);
    lean_dec_ref(v_a_3200_);
    return v_res_3207_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(
    mut v_config_3218_: u8,
    mut v_item_3219_: *mut LeanObject,
    mut v___y_3220_: *mut LeanObject,
    mut v___y_3221_: *mut LeanObject,
    mut v___y_3222_: *mut LeanObject,
    mut v___y_3223_: *mut LeanObject,
    mut v___y_3224_: *mut LeanObject,
    mut v___y_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_item_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: u8 = 0;
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3253_: u8 = 0;
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3257_: u8 = 0;
    let mut v_a_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3261_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v_a_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3269_: u8 = 0;
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3273_: u8 = 0;
    let mut v___x_3274_: u8 = 0;
    let mut v_value_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3280_: u8 = 0;
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3284_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3237_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5;
                v___x_3238_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
                    v_item_3219_,
                    v___x_3237_,
                    v___y_3220_,
                    v___y_3221_,
                    v___y_3222_,
                    v___y_3223_,
                    v___y_3224_,
                    v___y_3225_,
                );
                if lean_obj_tag(v___x_3238_) == 0 {
                    lean_dec_ref_known(v___x_3238_, 1);
                    v___x_3239_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3219_);
                    if v___x_3239_ == 0 {
                        v___x_3240_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3219_);
                        lean_inc_ref(v_item_3219_);
                        v___x_3241_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3219_);
                        v___x_3242_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__1;
                        v___x_3243_ = lean_string_dec_eq(v___x_3240_, v___x_3242_);
                        if v___x_3243_ == 0 {
                            v___x_3244_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__2;
                            v___x_3245_ = lean_string_dec_eq(v___x_3240_, v___x_3244_);
                            lean_dec_ref(v___x_3240_);
                            if v___x_3245_ == 0 {
                                lean_dec_ref(v_item_3219_);
                                v_item_3228_ = v___x_3241_;
                                v___y_3229_ = v___y_3220_;
                                v___y_3230_ = v___y_3221_;
                                v___y_3231_ = v___y_3222_;
                                v___y_3232_ = v___y_3223_;
                                v___y_3233_ = v___y_3224_;
                                v___y_3234_ = v___y_3225_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3246_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__3;
                                v___x_3247_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                    v_item_3219_,
                                    v___x_3246_,
                                    v___y_3220_,
                                    v___y_3221_,
                                    v___y_3222_,
                                    v___y_3223_,
                                    v___y_3224_,
                                    v___y_3225_,
                                );
                                if lean_obj_tag(v___x_3247_) == 0 {
                                    lean_dec_ref_known(v___x_3247_, 1);
                                    v___x_3248_ =
                                        l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3241_);
                                    if v___x_3248_ == 0 {
                                        lean_dec_ref(v_item_3219_);
                                        v_item_3228_ = v___x_3241_;
                                        v___y_3229_ = v___y_3220_;
                                        v___y_3230_ = v___y_3221_;
                                        v___y_3231_ = v___y_3222_;
                                        v___y_3232_ = v___y_3223_;
                                        v___y_3233_ = v___y_3224_;
                                        v___y_3234_ = v___y_3225_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec_ref(v___x_3241_);
                                        v___x_3249_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                            v_item_3219_,
                                            v___y_3220_,
                                            v___y_3221_,
                                            v___y_3222_,
                                            v___y_3223_,
                                            v___y_3224_,
                                            v___y_3225_,
                                        );
                                        if lean_obj_tag(v___x_3249_) == 0 {
                                            v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
                                            v_isSharedCheck_3257_ =
                                                (!lean_is_exclusive(v___x_3249_)) as u8;
                                            if v_isSharedCheck_3257_ == 0 {
                                                v___x_3252_ = v___x_3249_;
                                                v_isShared_3253_ = v_isSharedCheck_3257_;
                                                state = 2;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3250_);
                                                lean_dec(v___x_3249_);
                                                v___x_3252_ = lean_box(0);
                                                v_isShared_3253_ = v_isSharedCheck_3257_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            v_a_3258_ = lean_ctor_get(v___x_3249_, 0);
                                            v_isSharedCheck_3265_ =
                                                (!lean_is_exclusive(v___x_3249_)) as u8;
                                            if v_isSharedCheck_3265_ == 0 {
                                                v___x_3260_ = v___x_3249_;
                                                v_isShared_3261_ = v_isSharedCheck_3265_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3258_);
                                                lean_dec(v___x_3249_);
                                                v___x_3260_ = lean_box(0);
                                                v_isShared_3261_ = v_isSharedCheck_3265_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_3241_);
                                    lean_dec_ref(v_item_3219_);
                                    v_a_3266_ = lean_ctor_get(v___x_3247_, 0);
                                    v_isSharedCheck_3273_ = (!lean_is_exclusive(v___x_3247_)) as u8;
                                    if v_isSharedCheck_3273_ == 0 {
                                        v___x_3268_ = v___x_3247_;
                                        v_isShared_3269_ = v_isSharedCheck_3273_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3266_);
                                        lean_dec(v___x_3247_);
                                        v___x_3268_ = lean_box(0);
                                        v_isShared_3269_ = v_isSharedCheck_3273_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3240_);
                            v___x_3274_ =
                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3241_);
                            if v___x_3274_ == 0 {
                                lean_dec_ref(v_item_3219_);
                                v_item_3228_ = v___x_3241_;
                                v___y_3229_ = v___y_3220_;
                                v___y_3230_ = v___y_3221_;
                                v___y_3231_ = v___y_3222_;
                                v___y_3232_ = v___y_3223_;
                                v___y_3233_ = v___y_3224_;
                                v___y_3234_ = v___y_3225_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v___x_3241_);
                                v_value_3275_ = lean_ctor_get(v_item_3219_, 2);
                                lean_inc(v_value_3275_);
                                lean_dec_ref(v_item_3219_);
                                v___x_3276_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0(v_value_3275_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
                                return v___x_3276_;
                            }
                        }
                    } else {
                        v_item_3228_ = v_item_3219_;
                        v___y_3229_ = v___y_3220_;
                        v___y_3230_ = v___y_3221_;
                        v___y_3231_ = v___y_3222_;
                        v___y_3232_ = v___y_3223_;
                        v___y_3233_ = v___y_3224_;
                        v___y_3234_ = v___y_3225_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_item_3219_);
                    v_a_3277_ = lean_ctor_get(v___x_3238_, 0);
                    v_isSharedCheck_3284_ = (!lean_is_exclusive(v___x_3238_)) as u8;
                    if v_isSharedCheck_3284_ == 0 {
                        v___x_3279_ = v___x_3238_;
                        v_isShared_3280_ = v_isSharedCheck_3284_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3277_);
                        lean_dec(v___x_3238_);
                        v___x_3279_ = lean_box(0);
                        v_isShared_3280_ = v_isSharedCheck_3284_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3235_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___closed__0;
                v___x_3236_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
                    v_item_3228_,
                    v___x_3235_,
                    v___y_3229_,
                    v___y_3230_,
                    v___y_3231_,
                    v___y_3232_,
                    v___y_3233_,
                    v___y_3234_,
                );
                return v___x_3236_;
            }
            2 => {
                if v_isShared_3253_ == 0 {
                    v___x_3255_ = v___x_3252_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
                    v___x_3255_ = v_reuseFailAlloc_3256_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3255_;
            }
            4 => {
                if v_isShared_3261_ == 0 {
                    v___x_3263_ = v___x_3260_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
                    v___x_3263_ = v_reuseFailAlloc_3264_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3263_;
            }
            6 => {
                if v_isShared_3269_ == 0 {
                    v___x_3271_ = v___x_3268_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
                    v___x_3271_ = v_reuseFailAlloc_3272_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3271_;
            }
            8 => {
                if v_isShared_3280_ == 0 {
                    v___x_3282_ = v___x_3279_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0___boxed(
    mut v_config_3285_: *mut LeanObject,
    mut v_item_3286_: *mut LeanObject,
    mut v___y_3287_: *mut LeanObject,
    mut v___y_3288_: *mut LeanObject,
    mut v___y_3289_: *mut LeanObject,
    mut v___y_3290_: *mut LeanObject,
    mut v___y_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_3993__boxed_3294_: u8 = 0;
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_config_3993__boxed_3294_ = (lean_unbox(v_config_3285_) as u8);
    v_res_3295_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___lam__0(v_config_3993__boxed_3294_, v_item_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
    lean_dec(v___y_3292_);
    lean_dec_ref(v___y_3291_);
    lean_dec(v___y_3290_);
    lean_dec_ref(v___y_3289_);
    lean_dec(v___y_3288_);
    lean_dec_ref(v___y_3287_);
    return v_res_3295_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(
    mut v_e_3298_: *mut LeanObject,
    mut v___y_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
    mut v___y_3302_: *mut LeanObject,
    mut v___y_3303_: *mut LeanObject,
    mut v___y_3304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    v___x_3306_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3298_, v___y_3302_);
    return v___x_3306_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0___boxed(
    mut v_e_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
    mut v___y_3311_: *mut LeanObject,
    mut v___y_3312_: *mut LeanObject,
    mut v___y_3313_: *mut LeanObject,
    mut v___y_3314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3315_: *mut LeanObject = core::ptr::null_mut();
    v_res_3315_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__0(v_e_3307_, v___y_3308_, v___y_3309_, v___y_3310_, v___y_3311_, v___y_3312_, v___y_3313_);
    lean_dec(v___y_3313_);
    lean_dec_ref(v___y_3312_);
    lean_dec(v___y_3311_);
    lean_dec_ref(v___y_3310_);
    lean_dec(v___y_3309_);
    lean_dec_ref(v___y_3308_);
    return v_res_3315_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(
    mut v_00_u03b1_3316_: *mut LeanObject,
    mut v___y_3317_: *mut LeanObject,
    mut v___y_3318_: *mut LeanObject,
    mut v___y_3319_: *mut LeanObject,
    mut v___y_3320_: *mut LeanObject,
    mut v___y_3321_: *mut LeanObject,
    mut v___y_3322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    v___x_3324_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v___x_3324_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2___boxed(
    mut v_00_u03b1_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3333_: *mut LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
    lean_dec(v___y_3331_);
    lean_dec_ref(v___y_3330_);
    lean_dec(v___y_3329_);
    lean_dec_ref(v___y_3328_);
    lean_dec(v___y_3327_);
    lean_dec_ref(v___y_3326_);
    return v_res_3333_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(
    mut v_00_u03b1_3334_: *mut LeanObject,
    mut v_msg_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
    mut v___y_3337_: *mut LeanObject,
    mut v___y_3338_: *mut LeanObject,
    mut v___y_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    v___x_3343_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
    return v___x_3343_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1___boxed(
    mut v_00_u03b1_3344_: *mut LeanObject,
    mut v_msg_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
    mut v___y_3348_: *mut LeanObject,
    mut v___y_3349_: *mut LeanObject,
    mut v___y_3350_: *mut LeanObject,
    mut v___y_3351_: *mut LeanObject,
    mut v___y_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3353_: *mut LeanObject = core::ptr::null_mut();
    v_res_3353_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_3344_, v_msg_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
    lean_dec(v___y_3351_);
    lean_dec_ref(v___y_3350_);
    lean_dec(v___y_3349_);
    lean_dec_ref(v___y_3348_);
    lean_dec(v___y_3347_);
    lean_dec_ref(v___y_3346_);
    return v_res_3353_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(
    mut v_msgData_3354_: *mut LeanObject,
    mut v_macroStack_3355_: *mut LeanObject,
    mut v___y_3356_: *mut LeanObject,
    mut v___y_3357_: *mut LeanObject,
    mut v___y_3358_: *mut LeanObject,
    mut v___y_3359_: *mut LeanObject,
    mut v___y_3360_: *mut LeanObject,
    mut v___y_3361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    v___x_3363_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3354_, v_macroStack_3355_, v___y_3360_);
    return v___x_3363_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(
    mut v_msgData_3364_: *mut LeanObject,
    mut v_macroStack_3365_: *mut LeanObject,
    mut v___y_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3373_: *mut LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_3364_, v_macroStack_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_);
    lean_dec(v___y_3371_);
    lean_dec_ref(v___y_3370_);
    lean_dec(v___y_3369_);
    lean_dec_ref(v___y_3368_);
    lean_dec(v___y_3367_);
    lean_dec_ref(v___y_3366_);
    return v_res_3373_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    v___x_3374_ = lean_box(0);
    v___x_3375_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr___closed__5;
    v___x_3376_ = l_Lean_mkConst(v___x_3375_, v___x_3374_);
    return v___x_3376_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3377_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__0,
    );
    v___x_3378_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3378_, 0, v___x_3377_);
    return v___x_3378_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(
    mut v_cfg_3379_: u8,
    mut v_cfgItem_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    v___x_3388_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___closed__1,
    );
    v___x_3389_ = lean_box((v_cfg_3379_) as usize);
    v___x_3390_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v___x_3389_,
        v_cfgItem_3380_,
        v___x_3388_,
        v___y_3381_,
        v___y_3382_,
        v___y_3383_,
        v___y_3384_,
        v___y_3385_,
        v___y_3386_,
    );
    return v___x_3390_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0___boxed(
    mut v_cfg_3391_: *mut LeanObject,
    mut v_cfgItem_3392_: *mut LeanObject,
    mut v___y_3393_: *mut LeanObject,
    mut v___y_3394_: *mut LeanObject,
    mut v___y_3395_: *mut LeanObject,
    mut v___y_3396_: *mut LeanObject,
    mut v___y_3397_: *mut LeanObject,
    mut v___y_3398_: *mut LeanObject,
    mut v___y_3399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cfg_boxed_3400_: u8 = 0;
    let mut v_res_3401_: *mut LeanObject = core::ptr::null_mut();
    v_cfg_boxed_3400_ = (lean_unbox(v_cfg_3391_) as u8);
    v_res_3401_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___lam__0(
        v_cfg_boxed_3400_,
        v_cfgItem_3392_,
        v___y_3393_,
        v___y_3394_,
        v___y_3395_,
        v___y_3396_,
        v___y_3397_,
        v___y_3398_,
    );
    lean_dec(v___y_3398_);
    lean_dec_ref(v___y_3397_);
    lean_dec(v___y_3396_);
    lean_dec_ref(v___y_3395_);
    lean_dec(v___y_3394_);
    lean_dec_ref(v___y_3393_);
    lean_dec(v_cfgItem_3392_);
    return v_res_3401_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(
    mut v_cfg_3403_: *mut LeanObject,
    mut v_init_3404_: u8,
    mut v_logExceptions_3405_: u8,
    mut v_a_3406_: *mut LeanObject,
    mut v_a_3407_: *mut LeanObject,
    mut v_a_3408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_onErr_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eval_3411_: *mut LeanObject = core::ptr::null_mut();
    v_onErr_3410_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___closed__0;
    v_eval_3411_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem___closed__0;
    if v_logExceptions_3405_ == 0 {
        let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
        v___x_3412_ = lean_box((v_init_3404_) as usize);
        v___x_3413_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_3411_,
            v___x_3412_,
            v_cfg_3403_,
            v_onErr_3410_,
            v_logExceptions_3405_,
            v_a_3407_,
            v_a_3408_,
        );
        return v___x_3413_;
    } else {
        let mut v_recover_3414_: u8 = 0;
        let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
        v_recover_3414_ = lean_ctor_get_uint8(
            v_a_3406_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        );
        v___x_3415_ = lean_box((v_init_3404_) as usize);
        v___x_3416_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_3411_,
            v___x_3415_,
            v_cfg_3403_,
            v_onErr_3410_,
            v_recover_3414_,
            v_a_3407_,
            v_a_3408_,
        );
        return v___x_3416_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_elabImpossibleConfig___redArg___boxed(
    mut v_cfg_3417_: *mut LeanObject,
    mut v_init_3418_: *mut LeanObject,
    mut v_logExceptions_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
    mut v_a_3422_: *mut LeanObject,
    mut v_a_3423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_boxed_3424_: u8 = 0;
    let mut v_logExceptions_boxed_3425_: u8 = 0;
    let mut v_res_3426_: *mut LeanObject = core::ptr::null_mut();
    v_init_boxed_3424_ = (lean_unbox(v_init_3418_) as u8);
    v_logExceptions_boxed_3425_ = (lean_unbox(v_logExceptions_3419_) as u8);
    v_res_3426_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(
        v_cfg_3417_,
        v_init_boxed_3424_,
        v_logExceptions_boxed_3425_,
        v_a_3420_,
        v_a_3421_,
        v_a_3422_,
    );
    lean_dec(v_a_3422_);
    lean_dec_ref(v_a_3421_);
    lean_dec_ref(v_a_3420_);
    return v_res_3426_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabImpossibleConfig(
    mut v_cfg_3427_: *mut LeanObject,
    mut v_init_3428_: u8,
    mut v_logExceptions_3429_: u8,
    mut v_a_3430_: *mut LeanObject,
    mut v_a_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
    mut v_a_3433_: *mut LeanObject,
    mut v_a_3434_: *mut LeanObject,
    mut v_a_3435_: *mut LeanObject,
    mut v_a_3436_: *mut LeanObject,
    mut v_a_3437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    v___x_3439_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(
        v_cfg_3427_,
        v_init_3428_,
        v_logExceptions_3429_,
        v_a_3430_,
        v_a_3436_,
        v_a_3437_,
    );
    return v___x_3439_;
}
pub unsafe fn l_Lean_Elab_Tactic_elabImpossibleConfig___boxed(
    mut v_cfg_3440_: *mut LeanObject,
    mut v_init_3441_: *mut LeanObject,
    mut v_logExceptions_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
    mut v_a_3445_: *mut LeanObject,
    mut v_a_3446_: *mut LeanObject,
    mut v_a_3447_: *mut LeanObject,
    mut v_a_3448_: *mut LeanObject,
    mut v_a_3449_: *mut LeanObject,
    mut v_a_3450_: *mut LeanObject,
    mut v_a_3451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_boxed_3452_: u8 = 0;
    let mut v_logExceptions_boxed_3453_: u8 = 0;
    let mut v_res_3454_: *mut LeanObject = core::ptr::null_mut();
    v_init_boxed_3452_ = (lean_unbox(v_init_3441_) as u8);
    v_logExceptions_boxed_3453_ = (lean_unbox(v_logExceptions_3442_) as u8);
    v_res_3454_ = l_Lean_Elab_Tactic_elabImpossibleConfig(
        v_cfg_3440_,
        v_init_boxed_3452_,
        v_logExceptions_boxed_3453_,
        v_a_3443_,
        v_a_3444_,
        v_a_3445_,
        v_a_3446_,
        v_a_3447_,
        v_a_3448_,
        v_a_3449_,
        v_a_3450_,
    );
    lean_dec(v_a_3450_);
    lean_dec_ref(v_a_3449_);
    lean_dec(v_a_3448_);
    lean_dec_ref(v_a_3447_);
    lean_dec(v_a_3446_);
    lean_dec_ref(v_a_3445_);
    lean_dec(v_a_3444_);
    lean_dec_ref(v_a_3443_);
    return v_res_3454_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(
    mut v_e_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3472_: u8 = 0;
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v_unused_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3458_ = l_Lean_Expr_hasMVar(v_e_3455_);
                if v___x_3458_ == 0 {
                    v___x_3459_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3459_, 0, v_e_3455_);
                    return v___x_3459_;
                } else {
                    v___x_3460_ = lean_st_ref_get(v___y_3456_);
                    v_mctx_3461_ = lean_ctor_get(v___x_3460_, 0);
                    lean_inc_ref(v_mctx_3461_);
                    lean_dec(v___x_3460_);
                    v___x_3462_ = l_Lean_instantiateMVarsCore(v_mctx_3461_, v_e_3455_);
                    v_fst_3463_ = lean_ctor_get(v___x_3462_, 0);
                    lean_inc(v_fst_3463_);
                    v_snd_3464_ = lean_ctor_get(v___x_3462_, 1);
                    lean_inc(v_snd_3464_);
                    lean_dec_ref(v___x_3462_);
                    v___x_3465_ = lean_st_ref_take(v___y_3456_);
                    v_cache_3466_ = lean_ctor_get(v___x_3465_, 1);
                    v_zetaDeltaFVarIds_3467_ = lean_ctor_get(v___x_3465_, 2);
                    v_postponed_3468_ = lean_ctor_get(v___x_3465_, 3);
                    v_diag_3469_ = lean_ctor_get(v___x_3465_, 4);
                    v_isSharedCheck_3478_ = (!lean_is_exclusive(v___x_3465_)) as u8;
                    if v_isSharedCheck_3478_ == 0 {
                        v_unused_3479_ = lean_ctor_get(v___x_3465_, 0);
                        lean_dec(v_unused_3479_);
                        v___x_3471_ = v___x_3465_;
                        v_isShared_3472_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3469_);
                        lean_inc(v_postponed_3468_);
                        lean_inc(v_zetaDeltaFVarIds_3467_);
                        lean_inc(v_cache_3466_);
                        lean_dec(v___x_3465_);
                        v___x_3471_ = lean_box(0);
                        v_isShared_3472_ = v_isSharedCheck_3478_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3472_ == 0 {
                    lean_ctor_set(v___x_3471_, 0, v_snd_3464_);
                    v___x_3474_ = v___x_3471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_snd_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_cache_3466_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_zetaDeltaFVarIds_3467_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_postponed_3468_);
                    lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_diag_3469_);
                    v___x_3474_ = v_reuseFailAlloc_3477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3475_ = lean_st_ref_set(v___y_3456_, v___x_3474_);
                v___x_3476_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3476_, 0, v_fst_3463_);
                return v___x_3476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg___boxed(
    mut v_e_3480_: *mut LeanObject,
    mut v___y_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3483_: *mut LeanObject = core::ptr::null_mut();
    v_res_3483_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(
        v_e_3480_,
        v___y_3481_,
    );
    lean_dec(v___y_3481_);
    return v_res_3483_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(
    mut v_e_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
    mut v___y_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
    mut v___y_3492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    v___x_3494_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(
        v_e_3484_,
        v___y_3490_,
    );
    return v___x_3494_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___boxed(
    mut v_e_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
    mut v___y_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
    mut v___y_3502_: *mut LeanObject,
    mut v___y_3503_: *mut LeanObject,
    mut v___y_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3505_: *mut LeanObject = core::ptr::null_mut();
    v_res_3505_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0(
        v_e_3495_,
        v___y_3496_,
        v___y_3497_,
        v___y_3498_,
        v___y_3499_,
        v___y_3500_,
        v___y_3501_,
        v___y_3502_,
        v___y_3503_,
    );
    lean_dec(v___y_3503_);
    lean_dec_ref(v___y_3502_);
    lean_dec(v___y_3501_);
    lean_dec_ref(v___y_3500_);
    lean_dec(v___y_3499_);
    lean_dec_ref(v___y_3498_);
    lean_dec(v___y_3497_);
    lean_dec_ref(v___y_3496_);
    return v_res_3505_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(
    mut v_x_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3510_);
    lean_inc_ref(v___y_3509_);
    lean_inc(v___y_3508_);
    lean_inc_ref(v___y_3507_);
    v___x_3516_ = lean_apply_9(
        v_x_3506_,
        v___y_3507_,
        v___y_3508_,
        v___y_3509_,
        v___y_3510_,
        v___y_3511_,
        v___y_3512_,
        v___y_3513_,
        v___y_3514_,
        lean_box(0),
    );
    return v___x_3516_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed(
    mut v_x_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
    mut v___y_3526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3527_: *mut LeanObject = core::ptr::null_mut();
    v_res_3527_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0(v_x_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_);
    lean_dec(v___y_3521_);
    lean_dec_ref(v___y_3520_);
    lean_dec(v___y_3519_);
    lean_dec_ref(v___y_3518_);
    return v_res_3527_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(
    mut v_mvarId_3528_: *mut LeanObject,
    mut v_x_3529_: *mut LeanObject,
    mut v___y_3530_: *mut LeanObject,
    mut v___y_3531_: *mut LeanObject,
    mut v___y_3532_: *mut LeanObject,
    mut v___y_3533_: *mut LeanObject,
    mut v___y_3534_: *mut LeanObject,
    mut v___y_3535_: *mut LeanObject,
    mut v___y_3536_: *mut LeanObject,
    mut v___y_3537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3544_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3533_);
                lean_inc_ref(v___y_3532_);
                lean_inc(v___y_3531_);
                lean_inc_ref(v___y_3530_);
                v___f_3539_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_3539_, 0, v_x_3529_);
                lean_closure_set(v___f_3539_, 1, v___y_3530_);
                lean_closure_set(v___f_3539_, 2, v___y_3531_);
                lean_closure_set(v___f_3539_, 3, v___y_3532_);
                lean_closure_set(v___f_3539_, 4, v___y_3533_);
                v___x_3540_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_3528_,
                    v___f_3539_,
                    v___y_3534_,
                    v___y_3535_,
                    v___y_3536_,
                    v___y_3537_,
                );
                if lean_obj_tag(v___x_3540_) == 0 {
                    return v___x_3540_;
                } else {
                    v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
                    v_isSharedCheck_3548_ = (!lean_is_exclusive(v___x_3540_)) as u8;
                    if v_isSharedCheck_3548_ == 0 {
                        v___x_3543_ = v___x_3540_;
                        v_isShared_3544_ = v_isSharedCheck_3548_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3541_);
                        lean_dec(v___x_3540_);
                        v___x_3543_ = lean_box(0);
                        v_isShared_3544_ = v_isSharedCheck_3548_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3544_ == 0 {
                    v___x_3546_ = v___x_3543_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
                    v___x_3546_ = v_reuseFailAlloc_3547_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg___boxed(
    mut v_mvarId_3549_: *mut LeanObject,
    mut v_x_3550_: *mut LeanObject,
    mut v___y_3551_: *mut LeanObject,
    mut v___y_3552_: *mut LeanObject,
    mut v___y_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3560_: *mut LeanObject = core::ptr::null_mut();
    v_res_3560_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(
            v_mvarId_3549_,
            v_x_3550_,
            v___y_3551_,
            v___y_3552_,
            v___y_3553_,
            v___y_3554_,
            v___y_3555_,
            v___y_3556_,
            v___y_3557_,
            v___y_3558_,
        );
    lean_dec(v___y_3558_);
    lean_dec_ref(v___y_3557_);
    lean_dec(v___y_3556_);
    lean_dec_ref(v___y_3555_);
    lean_dec(v___y_3554_);
    lean_dec_ref(v___y_3553_);
    lean_dec(v___y_3552_);
    lean_dec_ref(v___y_3551_);
    return v_res_3560_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(
    mut v_00_u03b1_3561_: *mut LeanObject,
    mut v_mvarId_3562_: *mut LeanObject,
    mut v_x_3563_: *mut LeanObject,
    mut v___y_3564_: *mut LeanObject,
    mut v___y_3565_: *mut LeanObject,
    mut v___y_3566_: *mut LeanObject,
    mut v___y_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    v___x_3573_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(
            v_mvarId_3562_,
            v_x_3563_,
            v___y_3564_,
            v___y_3565_,
            v___y_3566_,
            v___y_3567_,
            v___y_3568_,
            v___y_3569_,
            v___y_3570_,
            v___y_3571_,
        );
    return v___x_3573_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___boxed(
    mut v_00_u03b1_3574_: *mut LeanObject,
    mut v_mvarId_3575_: *mut LeanObject,
    mut v_x_3576_: *mut LeanObject,
    mut v___y_3577_: *mut LeanObject,
    mut v___y_3578_: *mut LeanObject,
    mut v___y_3579_: *mut LeanObject,
    mut v___y_3580_: *mut LeanObject,
    mut v___y_3581_: *mut LeanObject,
    mut v___y_3582_: *mut LeanObject,
    mut v___y_3583_: *mut LeanObject,
    mut v___y_3584_: *mut LeanObject,
    mut v___y_3585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3586_: *mut LeanObject = core::ptr::null_mut();
    v_res_3586_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1(
        v_00_u03b1_3574_,
        v_mvarId_3575_,
        v_x_3576_,
        v___y_3577_,
        v___y_3578_,
        v___y_3579_,
        v___y_3580_,
        v___y_3581_,
        v___y_3582_,
        v___y_3583_,
        v___y_3584_,
    );
    lean_dec(v___y_3584_);
    lean_dec_ref(v___y_3583_);
    lean_dec(v___y_3582_);
    lean_dec_ref(v___y_3581_);
    lean_dec(v___y_3580_);
    lean_dec_ref(v___y_3579_);
    lean_dec(v___y_3578_);
    lean_dec_ref(v___y_3577_);
    return v_res_3586_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(
    mut v_kind_3587_: *mut LeanObject,
    mut v___y_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3608_: u8 = 0;
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut v_unused_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3590_ = lean_st_ref_get(v___y_3588_);
                v_auxDeclNGen_3591_ = lean_ctor_get(v___x_3590_, 3);
                lean_inc_ref(v_auxDeclNGen_3591_);
                lean_dec(v___x_3590_);
                v___x_3592_ = lean_st_ref_get(v___y_3588_);
                v_env_3593_ = lean_ctor_get(v___x_3592_, 0);
                lean_inc_ref(v_env_3593_);
                lean_dec(v___x_3592_);
                v___x_3594_ = l_Lean_DeclNameGenerator_mkUniqueName(
                    v_env_3593_,
                    v_auxDeclNGen_3591_,
                    v_kind_3587_,
                );
                v_fst_3595_ = lean_ctor_get(v___x_3594_, 0);
                lean_inc(v_fst_3595_);
                v_snd_3596_ = lean_ctor_get(v___x_3594_, 1);
                lean_inc(v_snd_3596_);
                lean_dec_ref(v___x_3594_);
                v___x_3597_ = lean_st_ref_take(v___y_3588_);
                v_env_3598_ = lean_ctor_get(v___x_3597_, 0);
                v_nextMacroScope_3599_ = lean_ctor_get(v___x_3597_, 1);
                v_ngen_3600_ = lean_ctor_get(v___x_3597_, 2);
                v_traceState_3601_ = lean_ctor_get(v___x_3597_, 4);
                v_cache_3602_ = lean_ctor_get(v___x_3597_, 5);
                v_messages_3603_ = lean_ctor_get(v___x_3597_, 6);
                v_infoState_3604_ = lean_ctor_get(v___x_3597_, 7);
                v_snapshotTasks_3605_ = lean_ctor_get(v___x_3597_, 8);
                v_isSharedCheck_3614_ = (!lean_is_exclusive(v___x_3597_)) as u8;
                if v_isSharedCheck_3614_ == 0 {
                    v_unused_3615_ = lean_ctor_get(v___x_3597_, 3);
                    lean_dec(v_unused_3615_);
                    v___x_3607_ = v___x_3597_;
                    v_isShared_3608_ = v_isSharedCheck_3614_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3605_);
                    lean_inc(v_infoState_3604_);
                    lean_inc(v_messages_3603_);
                    lean_inc(v_cache_3602_);
                    lean_inc(v_traceState_3601_);
                    lean_inc(v_ngen_3600_);
                    lean_inc(v_nextMacroScope_3599_);
                    lean_inc(v_env_3598_);
                    lean_dec(v___x_3597_);
                    v___x_3607_ = lean_box(0);
                    v_isShared_3608_ = v_isSharedCheck_3614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_3608_ == 0 {
                    lean_ctor_set(v___x_3607_, 3, v_snd_3596_);
                    v___x_3610_ = v___x_3607_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_env_3598_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 1, v_nextMacroScope_3599_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 2, v_ngen_3600_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 3, v_snd_3596_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 4, v_traceState_3601_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 5, v_cache_3602_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 6, v_messages_3603_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 7, v_infoState_3604_);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 8, v_snapshotTasks_3605_);
                    v___x_3610_ = v_reuseFailAlloc_3613_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3611_ = lean_st_ref_set(v___y_3588_, v___x_3610_);
                v___x_3612_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3612_, 0, v_fst_3595_);
                return v___x_3612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg___boxed(
    mut v_kind_3616_: *mut LeanObject,
    mut v___y_3617_: *mut LeanObject,
    mut v___y_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3619_: *mut LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(
        v_kind_3616_,
        v___y_3617_,
    );
    lean_dec(v___y_3617_);
    return v_res_3619_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(
    mut v_kind_3620_: *mut LeanObject,
    mut v___y_3621_: *mut LeanObject,
    mut v___y_3622_: *mut LeanObject,
    mut v___y_3623_: *mut LeanObject,
    mut v___y_3624_: *mut LeanObject,
    mut v___y_3625_: *mut LeanObject,
    mut v___y_3626_: *mut LeanObject,
    mut v___y_3627_: *mut LeanObject,
    mut v___y_3628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    v___x_3630_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(
        v_kind_3620_,
        v___y_3628_,
    );
    return v___x_3630_;
}
pub unsafe fn l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___boxed(
    mut v_kind_3631_: *mut LeanObject,
    mut v___y_3632_: *mut LeanObject,
    mut v___y_3633_: *mut LeanObject,
    mut v___y_3634_: *mut LeanObject,
    mut v___y_3635_: *mut LeanObject,
    mut v___y_3636_: *mut LeanObject,
    mut v___y_3637_: *mut LeanObject,
    mut v___y_3638_: *mut LeanObject,
    mut v___y_3639_: *mut LeanObject,
    mut v___y_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3641_: *mut LeanObject = core::ptr::null_mut();
    v_res_3641_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3(
        v_kind_3631_,
        v___y_3632_,
        v___y_3633_,
        v___y_3634_,
        v___y_3635_,
        v___y_3636_,
        v___y_3637_,
        v___y_3638_,
        v___y_3639_,
    );
    lean_dec(v___y_3639_);
    lean_dec_ref(v___y_3638_);
    lean_dec(v___y_3637_);
    lean_dec_ref(v___y_3636_);
    lean_dec(v___y_3635_);
    lean_dec_ref(v___y_3634_);
    lean_dec(v___y_3633_);
    lean_dec_ref(v___y_3632_);
    return v_res_3641_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(
    mut v_opts_3642_: *mut LeanObject,
    mut v_opt_3643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_name_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    v_name_3644_ = lean_ctor_get(v_opt_3643_, 0);
    v_defValue_3645_ = lean_ctor_get(v_opt_3643_, 1);
    v_map_3646_ = lean_ctor_get(v_opts_3642_, 0);
    v___x_3647_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3646_,
            v_name_3644_,
        );
    if lean_obj_tag(v___x_3647_) == 0 {
        lean_inc(v_defValue_3645_);
        return v_defValue_3645_;
    } else {
        let mut v_val_3648_: *mut LeanObject = core::ptr::null_mut();
        v_val_3648_ = lean_ctor_get(v___x_3647_, 0);
        lean_inc(v_val_3648_);
        lean_dec_ref_known(v___x_3647_, 1);
        if lean_obj_tag(v_val_3648_) == 3 {
            let mut v_v_3649_: *mut LeanObject = core::ptr::null_mut();
            v_v_3649_ = lean_ctor_get(v_val_3648_, 0);
            lean_inc(v_v_3649_);
            lean_dec_ref_known(v_val_3648_, 1);
            return v_v_3649_;
        } else {
            lean_dec(v_val_3648_);
            lean_inc(v_defValue_3645_);
            return v_defValue_3645_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5___boxed(
    mut v_opts_3650_: *mut LeanObject,
    mut v_opt_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3652_: *mut LeanObject = core::ptr::null_mut();
    v_res_3652_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(
        v_opts_3650_,
        v_opt_3651_,
    );
    lean_dec_ref(v_opt_3651_);
    lean_dec_ref(v_opts_3650_);
    return v_res_3652_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible___lam__0(
    mut v_a_3653_: *mut LeanObject,
    mut v___y_3654_: *mut LeanObject,
    mut v___y_3655_: *mut LeanObject,
    mut v___y_3656_: *mut LeanObject,
    mut v___y_3657_: *mut LeanObject,
    mut v___y_3658_: *mut LeanObject,
    mut v___y_3659_: *mut LeanObject,
    mut v___y_3660_: *mut LeanObject,
    mut v___y_3661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    v___x_3663_ = l_Lean_MVarId_getType(
        v_a_3653_,
        v___y_3658_,
        v___y_3659_,
        v___y_3660_,
        v___y_3661_,
    );
    if lean_obj_tag(v___x_3663_) == 0 {
        let mut v_a_3664_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
        v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
        lean_inc(v_a_3664_);
        lean_dec_ref_known(v___x_3663_, 1);
        v___x_3665_ =
            l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(
                v_a_3664_,
                v___y_3659_,
            );
        return v___x_3665_;
    } else {
        return v___x_3663_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed(
    mut v_a_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
    mut v___y_3671_: *mut LeanObject,
    mut v___y_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
    mut v___y_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3676_: *mut LeanObject = core::ptr::null_mut();
    v_res_3676_ = l_Lean_Elab_Tactic_evalImpossible___lam__0(
        v_a_3666_,
        v___y_3667_,
        v___y_3668_,
        v___y_3669_,
        v___y_3670_,
        v___y_3671_,
        v___y_3672_,
        v___y_3673_,
        v___y_3674_,
    );
    lean_dec(v___y_3674_);
    lean_dec_ref(v___y_3673_);
    lean_dec(v___y_3672_);
    lean_dec_ref(v___y_3671_);
    lean_dec(v___y_3670_);
    lean_dec_ref(v___y_3669_);
    lean_dec(v___y_3668_);
    lean_dec_ref(v___y_3667_);
    return v_res_3676_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible___lam__1(
    mut v___x_3677_: *mut LeanObject,
    mut v___y_3678_: *mut LeanObject,
    mut v___y_3679_: *mut LeanObject,
    mut v___y_3680_: *mut LeanObject,
    mut v___y_3681_: *mut LeanObject,
    mut v___y_3682_: *mut LeanObject,
    mut v___y_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_3677_,
        v___y_3678_,
        v___y_3679_,
        v___y_3680_,
        v___y_3681_,
        v___y_3682_,
        v___y_3683_,
        v___y_3684_,
        v___y_3685_,
    );
    if lean_obj_tag(v___x_3687_) == 0 {
        let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3687_, 1);
        v___x_3688_ = l_Lean_Elab_Tactic_done(
            v___y_3678_,
            v___y_3679_,
            v___y_3680_,
            v___y_3681_,
            v___y_3682_,
            v___y_3683_,
            v___y_3684_,
            v___y_3685_,
        );
        return v___x_3688_;
    } else {
        return v___x_3687_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed(
    mut v___x_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
    mut v___y_3694_: *mut LeanObject,
    mut v___y_3695_: *mut LeanObject,
    mut v___y_3696_: *mut LeanObject,
    mut v___y_3697_: *mut LeanObject,
    mut v___y_3698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3699_: *mut LeanObject = core::ptr::null_mut();
    v_res_3699_ = l_Lean_Elab_Tactic_evalImpossible___lam__1(
        v___x_3689_,
        v___y_3690_,
        v___y_3691_,
        v___y_3692_,
        v___y_3693_,
        v___y_3694_,
        v___y_3695_,
        v___y_3696_,
        v___y_3697_,
    );
    lean_dec(v___y_3697_);
    lean_dec_ref(v___y_3696_);
    lean_dec(v___y_3695_);
    lean_dec_ref(v___y_3694_);
    lean_dec(v___y_3693_);
    lean_dec_ref(v___y_3692_);
    lean_dec(v___y_3691_);
    lean_dec_ref(v___y_3690_);
    return v_res_3699_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible___lam__2(
    mut v_a_3700_: *mut LeanObject,
    mut v_trees_3701_: *mut LeanObject,
    mut v___y_3702_: *mut LeanObject,
    mut v___y_3703_: *mut LeanObject,
    mut v___y_3704_: *mut LeanObject,
    mut v___y_3705_: *mut LeanObject,
    mut v___y_3706_: *mut LeanObject,
    mut v___y_3707_: *mut LeanObject,
    mut v___y_3708_: *mut LeanObject,
    mut v___y_3709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3715_: u8 = 0;
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_a_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3709_);
                lean_inc_ref(v___y_3708_);
                lean_inc(v___y_3707_);
                lean_inc_ref(v___y_3706_);
                lean_inc(v___y_3705_);
                lean_inc_ref(v___y_3704_);
                lean_inc(v___y_3703_);
                lean_inc_ref(v___y_3702_);
                v___x_3711_ = lean_apply_9(
                    v_a_3700_,
                    v___y_3702_,
                    v___y_3703_,
                    v___y_3704_,
                    v___y_3705_,
                    v___y_3706_,
                    v___y_3707_,
                    v___y_3708_,
                    v___y_3709_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3711_) == 0 {
                    v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
                    v_isSharedCheck_3720_ = (!lean_is_exclusive(v___x_3711_)) as u8;
                    if v_isSharedCheck_3720_ == 0 {
                        v___x_3714_ = v___x_3711_;
                        v_isShared_3715_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3712_);
                        lean_dec(v___x_3711_);
                        v___x_3714_ = lean_box(0);
                        v_isShared_3715_ = v_isSharedCheck_3720_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_trees_3701_);
                    v_a_3721_ = lean_ctor_get(v___x_3711_, 0);
                    v_isSharedCheck_3728_ = (!lean_is_exclusive(v___x_3711_)) as u8;
                    if v_isSharedCheck_3728_ == 0 {
                        v___x_3723_ = v___x_3711_;
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3721_);
                        lean_dec(v___x_3711_);
                        v___x_3723_ = lean_box(0);
                        v_isShared_3724_ = v_isSharedCheck_3728_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3716_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3716_, 0, v_a_3712_);
                lean_ctor_set(v___x_3716_, 1, v_trees_3701_);
                if v_isShared_3715_ == 0 {
                    lean_ctor_set(v___x_3714_, 0, v___x_3716_);
                    v___x_3718_ = v___x_3714_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
                    v___x_3718_ = v_reuseFailAlloc_3719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3718_;
            }
            3 => {
                if v_isShared_3724_ == 0 {
                    v___x_3726_ = v___x_3723_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3726_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible___lam__2___boxed(
    mut v_a_3729_: *mut LeanObject,
    mut v_trees_3730_: *mut LeanObject,
    mut v___y_3731_: *mut LeanObject,
    mut v___y_3732_: *mut LeanObject,
    mut v___y_3733_: *mut LeanObject,
    mut v___y_3734_: *mut LeanObject,
    mut v___y_3735_: *mut LeanObject,
    mut v___y_3736_: *mut LeanObject,
    mut v___y_3737_: *mut LeanObject,
    mut v___y_3738_: *mut LeanObject,
    mut v___y_3739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3740_: *mut LeanObject = core::ptr::null_mut();
    v_res_3740_ = l_Lean_Elab_Tactic_evalImpossible___lam__2(
        v_a_3729_,
        v_trees_3730_,
        v___y_3731_,
        v___y_3732_,
        v___y_3733_,
        v___y_3734_,
        v___y_3735_,
        v___y_3736_,
        v___y_3737_,
        v___y_3738_,
    );
    lean_dec(v___y_3738_);
    lean_dec_ref(v___y_3737_);
    lean_dec(v___y_3736_);
    lean_dec_ref(v___y_3735_);
    lean_dec(v___y_3734_);
    lean_dec_ref(v___y_3733_);
    lean_dec(v___y_3732_);
    lean_dec_ref(v___y_3731_);
    return v_res_3740_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    v___x_3741_ = lean_unsigned_to_nat(32);
    v___x_3742_ = lean_mk_empty_array_with_capacity(v___x_3741_);
    v___x_3743_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3743_, 0, v___x_3742_);
    return v___x_3743_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3744_: usize = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    v___x_3744_ = 5usize;
    v___x_3745_ = lean_unsigned_to_nat(0);
    v___x_3746_ = lean_unsigned_to_nat(32);
    v___x_3747_ = lean_mk_empty_array_with_capacity(v___x_3746_);
    v___x_3748_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__0);
    v___x_3749_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3749_, 0, v___x_3748_);
    lean_ctor_set(v___x_3749_, 1, v___x_3747_);
    lean_ctor_set(v___x_3749_, 2, v___x_3745_);
    lean_ctor_set(v___x_3749_, 3, v___x_3745_);
    lean_ctor_set_usize(v___x_3749_, 4, v___x_3744_);
    return v___x_3749_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(
    mut v___y_3750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3767_: u8 = 0;
    let mut v_enabled_3768_: u8 = 0;
    let mut v_assignment_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3773_: u8 = 0;
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut v_unused_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3752_ = lean_st_ref_get(v___y_3750_);
                v_infoState_3753_ = lean_ctor_get(v___x_3752_, 7);
                lean_inc_ref(v_infoState_3753_);
                lean_dec(v___x_3752_);
                v_trees_3754_ = lean_ctor_get(v_infoState_3753_, 2);
                lean_inc_ref(v_trees_3754_);
                lean_dec_ref(v_infoState_3753_);
                v___x_3755_ = lean_st_ref_take(v___y_3750_);
                v_infoState_3756_ = lean_ctor_get(v___x_3755_, 7);
                v_env_3757_ = lean_ctor_get(v___x_3755_, 0);
                v_nextMacroScope_3758_ = lean_ctor_get(v___x_3755_, 1);
                v_ngen_3759_ = lean_ctor_get(v___x_3755_, 2);
                v_auxDeclNGen_3760_ = lean_ctor_get(v___x_3755_, 3);
                v_traceState_3761_ = lean_ctor_get(v___x_3755_, 4);
                v_cache_3762_ = lean_ctor_get(v___x_3755_, 5);
                v_messages_3763_ = lean_ctor_get(v___x_3755_, 6);
                v_snapshotTasks_3764_ = lean_ctor_get(v___x_3755_, 8);
                v_isSharedCheck_3785_ = (!lean_is_exclusive(v___x_3755_)) as u8;
                if v_isSharedCheck_3785_ == 0 {
                    v___x_3766_ = v___x_3755_;
                    v_isShared_3767_ = v_isSharedCheck_3785_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3764_);
                    lean_inc(v_infoState_3756_);
                    lean_inc(v_messages_3763_);
                    lean_inc(v_cache_3762_);
                    lean_inc(v_traceState_3761_);
                    lean_inc(v_auxDeclNGen_3760_);
                    lean_inc(v_ngen_3759_);
                    lean_inc(v_nextMacroScope_3758_);
                    lean_inc(v_env_3757_);
                    lean_dec(v___x_3755_);
                    v___x_3766_ = lean_box(0);
                    v_isShared_3767_ = v_isSharedCheck_3785_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_3768_ = lean_ctor_get_uint8(
                    v_infoState_3756_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_3769_ = lean_ctor_get(v_infoState_3756_, 0);
                v_lazyAssignment_3770_ = lean_ctor_get(v_infoState_3756_, 1);
                v_isSharedCheck_3783_ = (!lean_is_exclusive(v_infoState_3756_)) as u8;
                if v_isSharedCheck_3783_ == 0 {
                    v_unused_3784_ = lean_ctor_get(v_infoState_3756_, 2);
                    lean_dec(v_unused_3784_);
                    v___x_3772_ = v_infoState_3756_;
                    v_isShared_3773_ = v_isSharedCheck_3783_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_3770_);
                    lean_inc(v_assignment_3769_);
                    lean_dec(v_infoState_3756_);
                    v___x_3772_ = lean_box(0);
                    v_isShared_3773_ = v_isSharedCheck_3783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3774_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___closed__1);
                if v_isShared_3773_ == 0 {
                    lean_ctor_set(v___x_3772_, 2, v___x_3774_);
                    v___x_3776_ = v___x_3772_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_assignment_3769_);
                    lean_ctor_set(v_reuseFailAlloc_3782_, 1, v_lazyAssignment_3770_);
                    lean_ctor_set(v_reuseFailAlloc_3782_, 2, v___x_3774_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3782_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_3768_,
                    );
                    v___x_3776_ = v_reuseFailAlloc_3782_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3767_ == 0 {
                    lean_ctor_set(v___x_3766_, 7, v___x_3776_);
                    v___x_3778_ = v___x_3766_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_env_3757_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 1, v_nextMacroScope_3758_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 2, v_ngen_3759_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 3, v_auxDeclNGen_3760_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 4, v_traceState_3761_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 5, v_cache_3762_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 6, v_messages_3763_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 7, v___x_3776_);
                    lean_ctor_set(v_reuseFailAlloc_3781_, 8, v_snapshotTasks_3764_);
                    v___x_3778_ = v_reuseFailAlloc_3781_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3779_ = lean_st_ref_set(v___y_3750_, v___x_3778_);
                v___x_3780_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3780_, 0, v_trees_3754_);
                return v___x_3780_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg___boxed(
    mut v___y_3786_: *mut LeanObject,
    mut v___y_3787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3788_: *mut LeanObject = core::ptr::null_mut();
    v_res_3788_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_3786_);
    lean_dec(v___y_3786_);
    return v_res_3788_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(
    mut v___y_3789_: *mut LeanObject,
    mut v_mkInfoTree_3790_: *mut LeanObject,
    mut v___y_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
    mut v___y_3793_: *mut LeanObject,
    mut v___y_3794_: *mut LeanObject,
    mut v___y_3795_: *mut LeanObject,
    mut v___y_3796_: *mut LeanObject,
    mut v___y_3797_: *mut LeanObject,
    mut v_a_3798_: *mut LeanObject,
    mut v_a_x3f_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3808_: u8 = 0;
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v_enabled_3822_: u8 = 0;
    let mut v_assignment_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut v_unused_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3842_: u8 = 0;
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut v_a_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3801_ = lean_st_ref_get(v___y_3789_);
                v_infoState_3802_ = lean_ctor_get(v___x_3801_, 7);
                lean_inc_ref(v_infoState_3802_);
                lean_dec(v___x_3801_);
                v_trees_3803_ = lean_ctor_get(v_infoState_3802_, 2);
                lean_inc_ref(v_trees_3803_);
                lean_dec_ref(v_infoState_3802_);
                lean_inc(v___y_3789_);
                lean_inc_ref(v___y_3797_);
                lean_inc(v___y_3796_);
                lean_inc_ref(v___y_3795_);
                lean_inc(v___y_3794_);
                lean_inc_ref(v___y_3793_);
                lean_inc(v___y_3792_);
                lean_inc_ref(v___y_3791_);
                v___x_3804_ = lean_apply_10(
                    v_mkInfoTree_3790_,
                    v_trees_3803_,
                    v___y_3791_,
                    v___y_3792_,
                    v___y_3793_,
                    v___y_3794_,
                    v___y_3795_,
                    v___y_3796_,
                    v___y_3797_,
                    v___y_3789_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3804_) == 0 {
                    v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
                    v_isSharedCheck_3843_ = (!lean_is_exclusive(v___x_3804_)) as u8;
                    if v_isSharedCheck_3843_ == 0 {
                        v___x_3807_ = v___x_3804_;
                        v_isShared_3808_ = v_isSharedCheck_3843_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3805_);
                        lean_dec(v___x_3804_);
                        v___x_3807_ = lean_box(0);
                        v_isShared_3808_ = v_isSharedCheck_3843_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_3798_);
                    v_a_3844_ = lean_ctor_get(v___x_3804_, 0);
                    v_isSharedCheck_3851_ = (!lean_is_exclusive(v___x_3804_)) as u8;
                    if v_isSharedCheck_3851_ == 0 {
                        v___x_3846_ = v___x_3804_;
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3844_);
                        lean_dec(v___x_3804_);
                        v___x_3846_ = lean_box(0);
                        v_isShared_3847_ = v_isSharedCheck_3851_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3809_ = lean_st_ref_take(v___y_3789_);
                v_infoState_3810_ = lean_ctor_get(v___x_3809_, 7);
                v_env_3811_ = lean_ctor_get(v___x_3809_, 0);
                v_nextMacroScope_3812_ = lean_ctor_get(v___x_3809_, 1);
                v_ngen_3813_ = lean_ctor_get(v___x_3809_, 2);
                v_auxDeclNGen_3814_ = lean_ctor_get(v___x_3809_, 3);
                v_traceState_3815_ = lean_ctor_get(v___x_3809_, 4);
                v_cache_3816_ = lean_ctor_get(v___x_3809_, 5);
                v_messages_3817_ = lean_ctor_get(v___x_3809_, 6);
                v_snapshotTasks_3818_ = lean_ctor_get(v___x_3809_, 8);
                v_isSharedCheck_3842_ = (!lean_is_exclusive(v___x_3809_)) as u8;
                if v_isSharedCheck_3842_ == 0 {
                    v___x_3820_ = v___x_3809_;
                    v_isShared_3821_ = v_isSharedCheck_3842_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3818_);
                    lean_inc(v_infoState_3810_);
                    lean_inc(v_messages_3817_);
                    lean_inc(v_cache_3816_);
                    lean_inc(v_traceState_3815_);
                    lean_inc(v_auxDeclNGen_3814_);
                    lean_inc(v_ngen_3813_);
                    lean_inc(v_nextMacroScope_3812_);
                    lean_inc(v_env_3811_);
                    lean_dec(v___x_3809_);
                    v___x_3820_ = lean_box(0);
                    v_isShared_3821_ = v_isSharedCheck_3842_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_3822_ = lean_ctor_get_uint8(
                    v_infoState_3810_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_3823_ = lean_ctor_get(v_infoState_3810_, 0);
                v_lazyAssignment_3824_ = lean_ctor_get(v_infoState_3810_, 1);
                v_isSharedCheck_3840_ = (!lean_is_exclusive(v_infoState_3810_)) as u8;
                if v_isSharedCheck_3840_ == 0 {
                    v_unused_3841_ = lean_ctor_get(v_infoState_3810_, 2);
                    lean_dec(v_unused_3841_);
                    v___x_3826_ = v_infoState_3810_;
                    v_isShared_3827_ = v_isSharedCheck_3840_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_lazyAssignment_3824_);
                    lean_inc(v_assignment_3823_);
                    lean_dec(v_infoState_3810_);
                    v___x_3826_ = lean_box(0);
                    v_isShared_3827_ = v_isSharedCheck_3840_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3828_ = l_Lean_PersistentArray_push___redArg(v_a_3798_, v_a_3805_);
                if v_isShared_3827_ == 0 {
                    lean_ctor_set(v___x_3826_, 2, v___x_3828_);
                    v___x_3830_ = v___x_3826_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_assignment_3823_);
                    lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_lazyAssignment_3824_);
                    lean_ctor_set(v_reuseFailAlloc_3839_, 2, v___x_3828_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3839_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_3822_,
                    );
                    v___x_3830_ = v_reuseFailAlloc_3839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3821_ == 0 {
                    lean_ctor_set(v___x_3820_, 7, v___x_3830_);
                    v___x_3832_ = v___x_3820_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_env_3811_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 1, v_nextMacroScope_3812_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 2, v_ngen_3813_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 3, v_auxDeclNGen_3814_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 4, v_traceState_3815_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 5, v_cache_3816_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 6, v_messages_3817_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 7, v___x_3830_);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 8, v_snapshotTasks_3818_);
                    v___x_3832_ = v_reuseFailAlloc_3838_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3833_ = lean_st_ref_set(v___y_3789_, v___x_3832_);
                v___x_3834_ = lean_box(0);
                if v_isShared_3808_ == 0 {
                    lean_ctor_set(v___x_3807_, 0, v___x_3834_);
                    v___x_3836_ = v___x_3807_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3837_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3834_);
                    v___x_3836_ = v_reuseFailAlloc_3837_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3836_;
            }
            7 => {
                if v_isShared_3847_ == 0 {
                    v___x_3849_ = v___x_3846_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
                    v___x_3849_ = v_reuseFailAlloc_3850_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3849_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0___boxed(
    mut v___y_3852_: *mut LeanObject,
    mut v_mkInfoTree_3853_: *mut LeanObject,
    mut v___y_3854_: *mut LeanObject,
    mut v___y_3855_: *mut LeanObject,
    mut v___y_3856_: *mut LeanObject,
    mut v___y_3857_: *mut LeanObject,
    mut v___y_3858_: *mut LeanObject,
    mut v___y_3859_: *mut LeanObject,
    mut v___y_3860_: *mut LeanObject,
    mut v_a_3861_: *mut LeanObject,
    mut v_a_x3f_3862_: *mut LeanObject,
    mut v___y_3863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3864_: *mut LeanObject = core::ptr::null_mut();
    v_res_3864_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_3852_, v_mkInfoTree_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v_a_3861_, v_a_x3f_3862_);
    lean_dec(v_a_x3f_3862_);
    lean_dec_ref(v___y_3860_);
    lean_dec(v___y_3859_);
    lean_dec_ref(v___y_3858_);
    lean_dec(v___y_3857_);
    lean_dec_ref(v___y_3856_);
    lean_dec(v___y_3855_);
    lean_dec_ref(v___y_3854_);
    lean_dec(v___y_3852_);
    return v_res_3864_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(
    mut v_x_3865_: *mut LeanObject,
    mut v_mkInfoTree_3866_: *mut LeanObject,
    mut v___y_3867_: *mut LeanObject,
    mut v___y_3868_: *mut LeanObject,
    mut v___y_3869_: *mut LeanObject,
    mut v___y_3870_: *mut LeanObject,
    mut v___y_3871_: *mut LeanObject,
    mut v___y_3872_: *mut LeanObject,
    mut v___y_3873_: *mut LeanObject,
    mut v___y_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_3878_: u8 = 0;
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_unused_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_reuseFailAlloc_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3907_: u8 = 0;
    let mut v_a_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3913_: u8 = 0;
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3917_: u8 = 0;
    let mut v_unused_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3922_: u8 = 0;
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3876_ = lean_st_ref_get(v___y_3874_);
                v_infoState_3877_ = lean_ctor_get(v___x_3876_, 7);
                lean_inc_ref(v_infoState_3877_);
                lean_dec(v___x_3876_);
                v_enabled_3878_ = lean_ctor_get_uint8(
                    v_infoState_3877_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_3877_);
                if v_enabled_3878_ == 0 {
                    lean_dec_ref(v_mkInfoTree_3866_);
                    lean_inc(v___y_3874_);
                    lean_inc_ref(v___y_3873_);
                    lean_inc(v___y_3872_);
                    lean_inc_ref(v___y_3871_);
                    lean_inc(v___y_3870_);
                    lean_inc_ref(v___y_3869_);
                    lean_inc(v___y_3868_);
                    lean_inc_ref(v___y_3867_);
                    v___x_3879_ = lean_apply_9(
                        v_x_3865_,
                        v___y_3867_,
                        v___y_3868_,
                        v___y_3869_,
                        v___y_3870_,
                        v___y_3871_,
                        v___y_3872_,
                        v___y_3873_,
                        v___y_3874_,
                        lean_box(0),
                    );
                    return v___x_3879_;
                } else {
                    v___x_3880_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_3874_);
                    v_a_3881_ = lean_ctor_get(v___x_3880_, 0);
                    lean_inc(v_a_3881_);
                    lean_dec_ref(v___x_3880_);
                    lean_inc(v___y_3874_);
                    lean_inc_ref(v___y_3873_);
                    lean_inc(v___y_3872_);
                    lean_inc_ref(v___y_3871_);
                    lean_inc(v___y_3870_);
                    lean_inc_ref(v___y_3869_);
                    lean_inc(v___y_3868_);
                    lean_inc_ref(v___y_3867_);
                    v_r_3882_ = lean_apply_9(
                        v_x_3865_,
                        v___y_3867_,
                        v___y_3868_,
                        v___y_3869_,
                        v___y_3870_,
                        v___y_3871_,
                        v___y_3872_,
                        v___y_3873_,
                        v___y_3874_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v_r_3882_) == 0 {
                        v_a_3883_ = lean_ctor_get(v_r_3882_, 0);
                        v_isSharedCheck_3907_ = (!lean_is_exclusive(v_r_3882_)) as u8;
                        if v_isSharedCheck_3907_ == 0 {
                            v___x_3885_ = v_r_3882_;
                            v_isShared_3886_ = v_isSharedCheck_3907_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3883_);
                            lean_dec(v_r_3882_);
                            v___x_3885_ = lean_box(0);
                            v_isShared_3886_ = v_isSharedCheck_3907_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3908_ = lean_ctor_get(v_r_3882_, 0);
                        lean_inc(v_a_3908_);
                        lean_dec_ref_known(v_r_3882_, 1);
                        v___x_3909_ = lean_box(0);
                        v___x_3910_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_3874_, v_mkInfoTree_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v_a_3881_, v___x_3909_);
                        if lean_obj_tag(v___x_3910_) == 0 {
                            v_isSharedCheck_3917_ = (!lean_is_exclusive(v___x_3910_)) as u8;
                            if v_isSharedCheck_3917_ == 0 {
                                v_unused_3918_ = lean_ctor_get(v___x_3910_, 0);
                                lean_dec(v_unused_3918_);
                                v___x_3912_ = v___x_3910_;
                                v_isShared_3913_ = v_isSharedCheck_3917_;
                                state = 7;
                                continue;
                            } else {
                                lean_dec(v___x_3910_);
                                v___x_3912_ = lean_box(0);
                                v_isShared_3913_ = v_isSharedCheck_3917_;
                                state = 7;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3908_);
                            v_a_3919_ = lean_ctor_get(v___x_3910_, 0);
                            v_isSharedCheck_3926_ = (!lean_is_exclusive(v___x_3910_)) as u8;
                            if v_isSharedCheck_3926_ == 0 {
                                v___x_3921_ = v___x_3910_;
                                v_isShared_3922_ = v_isSharedCheck_3926_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_3919_);
                                lean_dec(v___x_3910_);
                                v___x_3921_ = lean_box(0);
                                v_isShared_3922_ = v_isSharedCheck_3926_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                lean_inc(v_a_3883_);
                if v_isShared_3886_ == 0 {
                    lean_ctor_set_tag(v___x_3885_, 1);
                    v___x_3888_ = v___x_3885_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3883_);
                    v___x_3888_ = v_reuseFailAlloc_3906_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3889_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___lam__0(v___y_3874_, v_mkInfoTree_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v_a_3881_, v___x_3888_);
                lean_dec_ref(v___x_3888_);
                if lean_obj_tag(v___x_3889_) == 0 {
                    v_isSharedCheck_3896_ = (!lean_is_exclusive(v___x_3889_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v_unused_3897_ = lean_ctor_get(v___x_3889_, 0);
                        lean_dec(v_unused_3897_);
                        v___x_3891_ = v___x_3889_;
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_3889_);
                        v___x_3891_ = lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3883_);
                    v_a_3898_ = lean_ctor_get(v___x_3889_, 0);
                    v_isSharedCheck_3905_ = (!lean_is_exclusive(v___x_3889_)) as u8;
                    if v_isSharedCheck_3905_ == 0 {
                        v___x_3900_ = v___x_3889_;
                        v_isShared_3901_ = v_isSharedCheck_3905_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3898_);
                        lean_dec(v___x_3889_);
                        v___x_3900_ = lean_box(0);
                        v_isShared_3901_ = v_isSharedCheck_3905_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3892_ == 0 {
                    lean_ctor_set(v___x_3891_, 0, v_a_3883_);
                    v___x_3894_ = v___x_3891_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3883_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3894_;
            }
            5 => {
                if v_isShared_3901_ == 0 {
                    v___x_3903_ = v___x_3900_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
                    v___x_3903_ = v_reuseFailAlloc_3904_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3903_;
            }
            7 => {
                if v_isShared_3913_ == 0 {
                    lean_ctor_set_tag(v___x_3912_, 1);
                    lean_ctor_set(v___x_3912_, 0, v_a_3908_);
                    v___x_3915_ = v___x_3912_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3908_);
                    v___x_3915_ = v_reuseFailAlloc_3916_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3915_;
            }
            9 => {
                if v_isShared_3922_ == 0 {
                    v___x_3924_ = v___x_3921_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg___boxed(
    mut v_x_3927_: *mut LeanObject,
    mut v_mkInfoTree_3928_: *mut LeanObject,
    mut v___y_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
    mut v___y_3931_: *mut LeanObject,
    mut v___y_3932_: *mut LeanObject,
    mut v___y_3933_: *mut LeanObject,
    mut v___y_3934_: *mut LeanObject,
    mut v___y_3935_: *mut LeanObject,
    mut v___y_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3938_: *mut LeanObject = core::ptr::null_mut();
    v_res_3938_ =
        l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(
            v_x_3927_,
            v_mkInfoTree_3928_,
            v___y_3929_,
            v___y_3930_,
            v___y_3931_,
            v___y_3932_,
            v___y_3933_,
            v___y_3934_,
            v___y_3935_,
            v___y_3936_,
        );
    lean_dec(v___y_3936_);
    lean_dec_ref(v___y_3935_);
    lean_dec(v___y_3934_);
    lean_dec_ref(v___y_3933_);
    lean_dec(v___y_3932_);
    lean_dec_ref(v___y_3931_);
    lean_dec(v___y_3930_);
    lean_dec_ref(v___y_3929_);
    return v_res_3938_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(
    mut v_o_3942_: *mut LeanObject,
    mut v_k_3943_: *mut LeanObject,
    mut v_v_3944_: u8,
) -> *mut LeanObject {
    let mut v_map_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3946_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: u8 = 0;
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_3945_ = lean_ctor_get(v_o_3942_, 0);
                v_hasTrace_3946_ = lean_ctor_get_uint8(
                    v_o_3942_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_3960_ = (!lean_is_exclusive(v_o_3942_)) as u8;
                if v_isSharedCheck_3960_ == 0 {
                    v___x_3948_ = v_o_3942_;
                    v_isShared_3949_ = v_isSharedCheck_3960_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_3945_);
                    lean_dec(v_o_3942_);
                    v___x_3948_ = lean_box(0);
                    v_isShared_3949_ = v_isSharedCheck_3960_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3950_ = lean_alloc_ctor(1, 0, (1) as u32);
                lean_ctor_set_uint8(v___x_3950_, 0 as u32, v_v_3944_);
                lean_inc(v_k_3943_);
                v___x_3951_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3943_, v___x_3950_, v_map_3945_);
                if v_hasTrace_3946_ == 0 {
                    v___x_3952_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___closed__1;
                    v___x_3953_ = l_Lean_Name_isPrefixOf(v___x_3952_, v_k_3943_);
                    lean_dec(v_k_3943_);
                    if v_isShared_3949_ == 0 {
                        lean_ctor_set(v___x_3948_, 0, v___x_3951_);
                        v___x_3955_ = v___x_3948_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3951_);
                        v___x_3955_ = v_reuseFailAlloc_3956_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_3943_);
                    if v_isShared_3949_ == 0 {
                        lean_ctor_set(v___x_3948_, 0, v___x_3951_);
                        v___x_3958_ = v___x_3948_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3951_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_3959_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_3946_,
                        );
                        v___x_3958_ = v_reuseFailAlloc_3959_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_3955_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_3953_,
                );
                return v___x_3955_;
            }
            3 => {
                return v___x_3958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5___boxed(
    mut v_o_3961_: *mut LeanObject,
    mut v_k_3962_: *mut LeanObject,
    mut v_v_3963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_3964_: u8 = 0;
    let mut v_res_3965_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_3964_ = (lean_unbox(v_v_3963_) as u8);
    v_res_3965_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(v_o_3961_, v_k_3962_, v_v_boxed_3964_);
    return v_res_3965_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(
    mut v_opts_3966_: *mut LeanObject,
    mut v_opt_3967_: *mut LeanObject,
    mut v_val_3968_: u8,
) -> *mut LeanObject {
    let mut v_name_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    v_name_3969_ = lean_ctor_get(v_opt_3967_, 0);
    lean_inc(v_name_3969_);
    lean_dec_ref(v_opt_3967_);
    v___x_3970_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4_spec__5(v_opts_3966_, v_name_3969_, v_val_3968_);
    return v___x_3970_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4___boxed(
    mut v_opts_3971_: *mut LeanObject,
    mut v_opt_3972_: *mut LeanObject,
    mut v_val_3973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_3974_: u8 = 0;
    let mut v_res_3975_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_3974_ = (lean_unbox(v_val_3973_) as u8);
    v_res_3975_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(
        v_opts_3971_,
        v_opt_3972_,
        v_val_boxed_3974_,
    );
    return v_res_3975_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(
    mut v_msg_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3992_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3982_ = lean_ctor_get(v___y_3979_, 5);
                v___x_3983_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig_evalExpr_spec__1_spec__1(v_msg_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
                v_a_3984_ = lean_ctor_get(v___x_3983_, 0);
                v_isSharedCheck_3992_ = (!lean_is_exclusive(v___x_3983_)) as u8;
                if v_isSharedCheck_3992_ == 0 {
                    v___x_3986_ = v___x_3983_;
                    v_isShared_3987_ = v_isSharedCheck_3992_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3984_);
                    lean_dec(v___x_3983_);
                    v___x_3986_ = lean_box(0);
                    v_isShared_3987_ = v_isSharedCheck_3992_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3982_);
                v___x_3988_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3988_, 0, v_ref_3982_);
                lean_ctor_set(v___x_3988_, 1, v_a_3984_);
                if v_isShared_3987_ == 0 {
                    lean_ctor_set_tag(v___x_3986_, 1);
                    lean_ctor_set(v___x_3986_, 0, v___x_3988_);
                    v___x_3990_ = v___x_3986_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3988_);
                    v___x_3990_ = v_reuseFailAlloc_3991_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3990_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg___boxed(
    mut v_msg_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3999_: *mut LeanObject = core::ptr::null_mut();
    v_res_3999_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
    lean_dec(v___y_3997_);
    lean_dec_ref(v___y_3996_);
    lean_dec(v___y_3995_);
    lean_dec_ref(v___y_3994_);
    return v_res_3999_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(
    mut v_ref_4000_: *mut LeanObject,
    mut v_msg_4001_: *mut LeanObject,
    mut v___y_4002_: *mut LeanObject,
    mut v___y_4003_: *mut LeanObject,
    mut v___y_4004_: *mut LeanObject,
    mut v___y_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4023_: u8 = 0;
    let mut v_cancelTk_x3f_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4025_: u8 = 0;
    let mut v_inheritedTraceOptions_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_4011_ = lean_ctor_get(v___y_4008_, 0);
    v_fileMap_4012_ = lean_ctor_get(v___y_4008_, 1);
    v_options_4013_ = lean_ctor_get(v___y_4008_, 2);
    v_currRecDepth_4014_ = lean_ctor_get(v___y_4008_, 3);
    v_maxRecDepth_4015_ = lean_ctor_get(v___y_4008_, 4);
    v_ref_4016_ = lean_ctor_get(v___y_4008_, 5);
    v_currNamespace_4017_ = lean_ctor_get(v___y_4008_, 6);
    v_openDecls_4018_ = lean_ctor_get(v___y_4008_, 7);
    v_initHeartbeats_4019_ = lean_ctor_get(v___y_4008_, 8);
    v_maxHeartbeats_4020_ = lean_ctor_get(v___y_4008_, 9);
    v_quotContext_4021_ = lean_ctor_get(v___y_4008_, 10);
    v_currMacroScope_4022_ = lean_ctor_get(v___y_4008_, 11);
    v_diag_4023_ = lean_ctor_get_uint8(
        v___y_4008_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4024_ = lean_ctor_get(v___y_4008_, 12);
    v_suppressElabErrors_4025_ = lean_ctor_get_uint8(
        v___y_4008_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4026_ = lean_ctor_get(v___y_4008_, 13);
    v_ref_4027_ = l_Lean_replaceRef(v_ref_4000_, v_ref_4016_);
    lean_inc_ref(v_inheritedTraceOptions_4026_);
    lean_inc(v_cancelTk_x3f_4024_);
    lean_inc(v_currMacroScope_4022_);
    lean_inc(v_quotContext_4021_);
    lean_inc(v_maxHeartbeats_4020_);
    lean_inc(v_initHeartbeats_4019_);
    lean_inc(v_openDecls_4018_);
    lean_inc(v_currNamespace_4017_);
    lean_inc(v_maxRecDepth_4015_);
    lean_inc(v_currRecDepth_4014_);
    lean_inc_ref(v_options_4013_);
    lean_inc_ref(v_fileMap_4012_);
    lean_inc_ref(v_fileName_4011_);
    v___x_4028_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_4028_, 0, v_fileName_4011_);
    lean_ctor_set(v___x_4028_, 1, v_fileMap_4012_);
    lean_ctor_set(v___x_4028_, 2, v_options_4013_);
    lean_ctor_set(v___x_4028_, 3, v_currRecDepth_4014_);
    lean_ctor_set(v___x_4028_, 4, v_maxRecDepth_4015_);
    lean_ctor_set(v___x_4028_, 5, v_ref_4027_);
    lean_ctor_set(v___x_4028_, 6, v_currNamespace_4017_);
    lean_ctor_set(v___x_4028_, 7, v_openDecls_4018_);
    lean_ctor_set(v___x_4028_, 8, v_initHeartbeats_4019_);
    lean_ctor_set(v___x_4028_, 9, v_maxHeartbeats_4020_);
    lean_ctor_set(v___x_4028_, 10, v_quotContext_4021_);
    lean_ctor_set(v___x_4028_, 11, v_currMacroScope_4022_);
    lean_ctor_set(v___x_4028_, 12, v_cancelTk_x3f_4024_);
    lean_ctor_set(v___x_4028_, 13, v_inheritedTraceOptions_4026_);
    lean_ctor_set_uint8(
        v___x_4028_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_4023_,
    );
    lean_ctor_set_uint8(
        v___x_4028_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4025_,
    );
    v___x_4029_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_4001_, v___y_4006_, v___y_4007_, v___x_4028_, v___y_4009_);
    lean_dec_ref_known(v___x_4028_, 14);
    return v___x_4029_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg___boxed(
    mut v_ref_4030_: *mut LeanObject,
    mut v_msg_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
    mut v___y_4036_: *mut LeanObject,
    mut v___y_4037_: *mut LeanObject,
    mut v___y_4038_: *mut LeanObject,
    mut v___y_4039_: *mut LeanObject,
    mut v___y_4040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4041_: *mut LeanObject = core::ptr::null_mut();
    v_res_4041_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(
        v_ref_4030_,
        v_msg_4031_,
        v___y_4032_,
        v___y_4033_,
        v___y_4034_,
        v___y_4035_,
        v___y_4036_,
        v___y_4037_,
        v___y_4038_,
        v___y_4039_,
    );
    lean_dec(v___y_4039_);
    lean_dec_ref(v___y_4038_);
    lean_dec(v___y_4037_);
    lean_dec_ref(v___y_4036_);
    lean_dec(v___y_4035_);
    lean_dec_ref(v___y_4034_);
    lean_dec(v___y_4033_);
    lean_dec_ref(v___y_4032_);
    lean_dec(v_ref_4030_);
    return v_res_4041_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__0() -> *mut LeanObject {
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    v___x_4042_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4042_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__1() -> *mut LeanObject {
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    v___x_4043_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__0_once),
        _init_l_Lean_Elab_Tactic_evalImpossible___closed__0,
    );
    v___x_4044_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4044_, 0, v___x_4043_);
    return v___x_4044_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__2() -> *mut LeanObject {
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    v___x_4045_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__1_once),
        _init_l_Lean_Elab_Tactic_evalImpossible___closed__1,
    );
    v___x_4046_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4046_, 0, v___x_4045_);
    lean_ctor_set(v___x_4046_, 1, v___x_4045_);
    return v___x_4046_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__3() -> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    v___x_4047_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4047_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__4() -> *mut LeanObject {
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    v___x_4048_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__3_once),
        _init_l_Lean_Elab_Tactic_evalImpossible___closed__3,
    );
    v___x_4049_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4049_, 0, v___x_4048_);
    return v___x_4049_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__5() -> *mut LeanObject {
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    v___x_4050_ = lean_unsigned_to_nat(32);
    v___x_4051_ = lean_mk_empty_array_with_capacity(v___x_4050_);
    v___x_4052_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4052_, 0, v___x_4051_);
    return v___x_4052_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__6() -> *mut LeanObject {
    let mut v___x_4053_: usize = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    v___x_4053_ = 5usize;
    v___x_4054_ = lean_unsigned_to_nat(0);
    v___x_4055_ = lean_unsigned_to_nat(32);
    v___x_4056_ = lean_mk_empty_array_with_capacity(v___x_4055_);
    v___x_4057_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__5_once),
        _init_l_Lean_Elab_Tactic_evalImpossible___closed__5,
    );
    v___x_4058_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4058_, 0, v___x_4057_);
    lean_ctor_set(v___x_4058_, 1, v___x_4056_);
    lean_ctor_set(v___x_4058_, 2, v___x_4054_);
    lean_ctor_set(v___x_4058_, 3, v___x_4054_);
    lean_ctor_set_usize(v___x_4058_, 4, v___x_4053_);
    return v___x_4058_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__7() -> *mut LeanObject {
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    v___x_4059_ = lean_box(1);
    v___x_4060_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__6_once),
        _init_l_Lean_Elab_Tactic_evalImpossible___closed__6,
    );
    v___x_4061_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__4_once),
        _init_l_Lean_Elab_Tactic_evalImpossible___closed__4,
    );
    v___x_4062_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4062_, 0, v___x_4061_);
    lean_ctor_set(v___x_4062_, 1, v___x_4060_);
    lean_ctor_set(v___x_4062_, 2, v___x_4059_);
    return v___x_4062_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_evalImpossible___closed__12() -> *mut LeanObject {
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    v___x_4069_ = l_Lean_Elab_Tactic_evalImpossible___closed__11;
    v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
    return v___x_4070_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible(
    mut v_stx_4071_: *mut LeanObject,
    mut v_a_4072_: *mut LeanObject,
    mut v_a_4073_: *mut LeanObject,
    mut v_a_4074_: *mut LeanObject,
    mut v_a_4075_: *mut LeanObject,
    mut v_a_4076_: *mut LeanObject,
    mut v_a_4077_: *mut LeanObject,
    mut v_a_4078_: *mut LeanObject,
    mut v_a_4079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4088_: u8 = 0;
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_unused_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4102_: u8 = 0;
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4106_: u8 = 0;
    let mut v_unused_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: u8 = 0;
    let mut v___y_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4117_: u8 = 0;
    let mut v_fileName_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4129_: u8 = 0;
    let mut v_inheritedTraceOptions_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4141_: u8 = 0;
    let mut v___y_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4155_: u8 = 0;
    let mut v_inheritedTraceOptions_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4164_: u8 = 0;
    let mut v___y_4165_: u8 = 0;
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4177_: u8 = 0;
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4184_: u8 = 0;
    let mut v_unused_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: u8 = 0;
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: u8 = 0;
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4234_: u8 = 0;
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v_levelParams_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4272_: u8 = 0;
    let mut v_inheritedTraceOptions_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4286_: u8 = 0;
    let mut v_reuseFailAlloc_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4289_: u8 = 0;
    let mut v_a_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4294_: u8 = 0;
    let mut v_unused_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4299_: u8 = 0;
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4303_: u8 = 0;
    let mut v_a_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4307_: u8 = 0;
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v_a_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_a_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v___x_4329_: u8 = 0;
    let mut v_kw_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4342_: u8 = 0;
    let mut v_a_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4350_: u8 = 0;
    let mut v_a_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4354_: u8 = 0;
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4358_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4109_ = lean_unsigned_to_nat(1);
                v___x_4110_ = l_Lean_Syntax_getArg(v_stx_4071_, v___x_4109_);
                v___x_4111_ = 0;
                v___x_4186_ = 1;
                v___x_4187_ = l_Lean_Elab_Tactic_elabImpossibleConfig___redArg(
                    v___x_4110_,
                    v___x_4111_,
                    v___x_4186_,
                    v_a_4072_,
                    v_a_4078_,
                    v_a_4079_,
                );
                if lean_obj_tag(v___x_4187_) == 0 {
                    v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
                    lean_inc(v_a_4188_);
                    lean_dec_ref_known(v___x_4187_, 1);
                    v___x_4189_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                        v_a_4073_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_,
                    );
                    if lean_obj_tag(v___x_4189_) == 0 {
                        v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
                        lean_inc_n(v_a_4190_, 3);
                        lean_dec_ref_known(v___x_4189_, 1);
                        v___f_4191_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_evalImpossible___lam__0___boxed
                                as *mut core::ffi::c_void,
                            10,
                            1,
                        );
                        lean_closure_set(v___f_4191_, 0, v_a_4190_);
                        v___x_4192_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_evalImpossible_spec__1___redArg(v_a_4190_, v___f_4191_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
                        if lean_obj_tag(v___x_4192_) == 0 {
                            v_a_4193_ = lean_ctor_get(v___x_4192_, 0);
                            lean_inc(v_a_4193_);
                            lean_dec_ref_known(v___x_4192_, 1);
                            v___x_4194_ = lean_unsigned_to_nat(0);
                            v___x_4195_ = lean_unsigned_to_nat(2);
                            v___x_4196_ = l_Lean_Syntax_getArg(v_stx_4071_, v___x_4195_);
                            v___x_4197_ = lean_unsigned_to_nat(3);
                            v___x_4198_ = l_Lean_Syntax_getArg(v_stx_4071_, v___x_4197_);
                            v___f_4199_ = lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalImpossible___lam__1___boxed
                                    as *mut core::ffi::c_void,
                                10,
                                1,
                            );
                            lean_closure_set(v___f_4199_, 0, v___x_4198_);
                            v___x_4329_ = l_Lean_Expr_hasLevelMVar(v_a_4193_);
                            if v___x_4329_ == 0 {
                                v___y_4201_ = v_a_4072_;
                                v___y_4202_ = v_a_4073_;
                                v___y_4203_ = v_a_4074_;
                                v___y_4204_ = v_a_4075_;
                                v___y_4205_ = v_a_4076_;
                                v___y_4206_ = v_a_4077_;
                                v___y_4207_ = v_a_4078_;
                                v___y_4208_ = v_a_4079_;
                                state = 12;
                                continue;
                            } else {
                                lean_dec_ref(v___f_4199_);
                                lean_dec(v___x_4196_);
                                lean_dec(v_a_4190_);
                                lean_dec(v_a_4188_);
                                v_kw_4330_ = l_Lean_Syntax_getArg(v_stx_4071_, v___x_4194_);
                                v___x_4331_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_evalImpossible___closed__12
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Tactic_evalImpossible___closed__12_once
                                    ),
                                    _init_l_Lean_Elab_Tactic_evalImpossible___closed__12,
                                );
                                v___x_4332_ = l_Lean_indentExpr(v_a_4193_);
                                v___x_4333_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_4333_, 0, v___x_4331_);
                                lean_ctor_set(v___x_4333_, 1, v___x_4332_);
                                v___x_4334_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(v_kw_4330_, v___x_4333_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_, v_a_4076_, v_a_4077_, v_a_4078_, v_a_4079_);
                                lean_dec(v_kw_4330_);
                                return v___x_4334_;
                            }
                        } else {
                            lean_dec(v_a_4190_);
                            lean_dec(v_a_4188_);
                            v_a_4335_ = lean_ctor_get(v___x_4192_, 0);
                            v_isSharedCheck_4342_ = (!lean_is_exclusive(v___x_4192_)) as u8;
                            if v_isSharedCheck_4342_ == 0 {
                                v___x_4337_ = v___x_4192_;
                                v_isShared_4338_ = v_isSharedCheck_4342_;
                                state = 27;
                                continue;
                            } else {
                                lean_inc(v_a_4335_);
                                lean_dec(v___x_4192_);
                                v___x_4337_ = lean_box(0);
                                v_isShared_4338_ = v_isSharedCheck_4342_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4188_);
                        v_a_4343_ = lean_ctor_get(v___x_4189_, 0);
                        v_isSharedCheck_4350_ = (!lean_is_exclusive(v___x_4189_)) as u8;
                        if v_isSharedCheck_4350_ == 0 {
                            v___x_4345_ = v___x_4189_;
                            v_isShared_4346_ = v_isSharedCheck_4350_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_4343_);
                            lean_dec(v___x_4189_);
                            v___x_4345_ = lean_box(0);
                            v_isShared_4346_ = v_isSharedCheck_4350_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    v_a_4351_ = lean_ctor_get(v___x_4187_, 0);
                    v_isSharedCheck_4358_ = (!lean_is_exclusive(v___x_4187_)) as u8;
                    if v_isSharedCheck_4358_ == 0 {
                        v___x_4353_ = v___x_4187_;
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_4351_);
                        lean_dec(v___x_4187_);
                        v___x_4353_ = lean_box(0);
                        v_isShared_4354_ = v_isSharedCheck_4358_;
                        state = 31;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4085_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_4082_, v___y_4083_);
                if lean_obj_tag(v___x_4085_) == 0 {
                    v_isSharedCheck_4092_ = (!lean_is_exclusive(v___x_4085_)) as u8;
                    if v_isSharedCheck_4092_ == 0 {
                        v_unused_4093_ = lean_ctor_get(v___x_4085_, 0);
                        lean_dec(v_unused_4093_);
                        v___x_4087_ = v___x_4085_;
                        v_isShared_4088_ = v_isSharedCheck_4092_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_4085_);
                        v___x_4087_ = lean_box(0);
                        v_isShared_4088_ = v_isSharedCheck_4092_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_a_4084_);
                    return v___x_4085_;
                }
            }
            2 => {
                if v_isShared_4088_ == 0 {
                    lean_ctor_set_tag(v___x_4087_, 1);
                    lean_ctor_set(v___x_4087_, 0, v_a_4084_);
                    v___x_4090_ = v___x_4087_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4084_);
                    v___x_4090_ = v_reuseFailAlloc_4091_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4090_;
            }
            4 => {
                if lean_obj_tag(v___y_4097_) == 0 {
                    v_a_4098_ = lean_ctor_get(v___y_4097_, 0);
                    lean_inc(v_a_4098_);
                    lean_dec_ref_known(v___y_4097_, 1);
                    v___x_4099_ = l_Lean_Elab_Tactic_setGoals___redArg(v___y_4095_, v___y_4096_);
                    if lean_obj_tag(v___x_4099_) == 0 {
                        v_isSharedCheck_4106_ = (!lean_is_exclusive(v___x_4099_)) as u8;
                        if v_isSharedCheck_4106_ == 0 {
                            v_unused_4107_ = lean_ctor_get(v___x_4099_, 0);
                            lean_dec(v_unused_4107_);
                            v___x_4101_ = v___x_4099_;
                            v_isShared_4102_ = v_isSharedCheck_4106_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v___x_4099_);
                            v___x_4101_ = lean_box(0);
                            v_isShared_4102_ = v_isSharedCheck_4106_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4098_);
                        return v___x_4099_;
                    }
                } else {
                    v_a_4108_ = lean_ctor_get(v___y_4097_, 0);
                    lean_inc(v_a_4108_);
                    lean_dec_ref_known(v___y_4097_, 1);
                    v___y_4082_ = v___y_4095_;
                    v___y_4083_ = v___y_4096_;
                    v_a_4084_ = v_a_4108_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v_isShared_4102_ == 0 {
                    lean_ctor_set(v___x_4101_, 0, v_a_4098_);
                    v___x_4104_ = v___x_4101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4098_);
                    v___x_4104_ = v_reuseFailAlloc_4105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4104_;
            }
            7 => {
                v___x_4132_ = l_Lean_maxRecDepth;
                v___x_4133_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_evalImpossible_spec__5(
                    v___y_4115_,
                    v___x_4132_,
                );
                lean_inc_ref(v_inheritedTraceOptions_4130_);
                lean_inc(v_cancelTk_x3f_4128_);
                lean_inc(v_currMacroScope_4127_);
                lean_inc(v_quotContext_4126_);
                lean_inc(v_maxHeartbeats_4125_);
                lean_inc(v_initHeartbeats_4124_);
                lean_inc(v_openDecls_4123_);
                lean_inc(v_currNamespace_4122_);
                lean_inc(v_ref_4121_);
                lean_inc(v_currRecDepth_4120_);
                lean_inc_ref(v_fileMap_4119_);
                lean_inc_ref(v_fileName_4118_);
                v___x_4134_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_4134_, 0, v_fileName_4118_);
                lean_ctor_set(v___x_4134_, 1, v_fileMap_4119_);
                lean_ctor_set(v___x_4134_, 2, v___y_4115_);
                lean_ctor_set(v___x_4134_, 3, v_currRecDepth_4120_);
                lean_ctor_set(v___x_4134_, 4, v___x_4133_);
                lean_ctor_set(v___x_4134_, 5, v_ref_4121_);
                lean_ctor_set(v___x_4134_, 6, v_currNamespace_4122_);
                lean_ctor_set(v___x_4134_, 7, v_openDecls_4123_);
                lean_ctor_set(v___x_4134_, 8, v_initHeartbeats_4124_);
                lean_ctor_set(v___x_4134_, 9, v_maxHeartbeats_4125_);
                lean_ctor_set(v___x_4134_, 10, v_quotContext_4126_);
                lean_ctor_set(v___x_4134_, 11, v_currMacroScope_4127_);
                lean_ctor_set(v___x_4134_, 12, v_cancelTk_x3f_4128_);
                lean_ctor_set(v___x_4134_, 13, v_inheritedTraceOptions_4130_);
                lean_ctor_set_uint8(
                    v___x_4134_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v___y_4117_,
                );
                lean_ctor_set_uint8(
                    v___x_4134_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4129_,
                );
                v___x_4135_ = l_Lean_addDecl(v___y_4113_, v___x_4111_, v___x_4134_, v___y_4131_);
                lean_dec_ref_known(v___x_4134_, 14);
                v___y_4095_ = v___y_4114_;
                v___y_4096_ = v___y_4116_;
                v___y_4097_ = v___x_4135_;
                state = 4;
                continue;
            }
            8 => {
                v_fileName_4144_ = lean_ctor_get(v___y_4142_, 0);
                v_fileMap_4145_ = lean_ctor_get(v___y_4142_, 1);
                v_currRecDepth_4146_ = lean_ctor_get(v___y_4142_, 3);
                v_ref_4147_ = lean_ctor_get(v___y_4142_, 5);
                v_currNamespace_4148_ = lean_ctor_get(v___y_4142_, 6);
                v_openDecls_4149_ = lean_ctor_get(v___y_4142_, 7);
                v_initHeartbeats_4150_ = lean_ctor_get(v___y_4142_, 8);
                v_maxHeartbeats_4151_ = lean_ctor_get(v___y_4142_, 9);
                v_quotContext_4152_ = lean_ctor_get(v___y_4142_, 10);
                v_currMacroScope_4153_ = lean_ctor_get(v___y_4142_, 11);
                v_cancelTk_x3f_4154_ = lean_ctor_get(v___y_4142_, 12);
                v_suppressElabErrors_4155_ = lean_ctor_get_uint8(
                    v___y_4142_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4156_ = lean_ctor_get(v___y_4142_, 13);
                v___y_4113_ = v___y_4137_;
                v___y_4114_ = v___y_4138_;
                v___y_4115_ = v___y_4139_;
                v___y_4116_ = v___y_4140_;
                v___y_4117_ = v___y_4141_;
                v_fileName_4118_ = v_fileName_4144_;
                v_fileMap_4119_ = v_fileMap_4145_;
                v_currRecDepth_4120_ = v_currRecDepth_4146_;
                v_ref_4121_ = v_ref_4147_;
                v_currNamespace_4122_ = v_currNamespace_4148_;
                v_openDecls_4123_ = v_openDecls_4149_;
                v_initHeartbeats_4124_ = v_initHeartbeats_4150_;
                v_maxHeartbeats_4125_ = v_maxHeartbeats_4151_;
                v_quotContext_4126_ = v_quotContext_4152_;
                v_currMacroScope_4127_ = v_currMacroScope_4153_;
                v_cancelTk_x3f_4128_ = v_cancelTk_x3f_4154_;
                v_suppressElabErrors_4129_ = v_suppressElabErrors_4155_;
                v_inheritedTraceOptions_4130_ = v_inheritedTraceOptions_4156_;
                v___y_4131_ = v___y_4143_;
                state = 7;
                continue;
            }
            9 => {
                if v___y_4165_ == 0 {
                    v___x_4166_ = lean_st_ref_take(v___y_4159_);
                    v_env_4167_ = lean_ctor_get(v___x_4166_, 0);
                    v_nextMacroScope_4168_ = lean_ctor_get(v___x_4166_, 1);
                    v_ngen_4169_ = lean_ctor_get(v___x_4166_, 2);
                    v_auxDeclNGen_4170_ = lean_ctor_get(v___x_4166_, 3);
                    v_traceState_4171_ = lean_ctor_get(v___x_4166_, 4);
                    v_messages_4172_ = lean_ctor_get(v___x_4166_, 6);
                    v_infoState_4173_ = lean_ctor_get(v___x_4166_, 7);
                    v_snapshotTasks_4174_ = lean_ctor_get(v___x_4166_, 8);
                    v_isSharedCheck_4184_ = (!lean_is_exclusive(v___x_4166_)) as u8;
                    if v_isSharedCheck_4184_ == 0 {
                        v_unused_4185_ = lean_ctor_get(v___x_4166_, 5);
                        lean_dec(v_unused_4185_);
                        v___x_4176_ = v___x_4166_;
                        v_isShared_4177_ = v_isSharedCheck_4184_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_4174_);
                        lean_inc(v_infoState_4173_);
                        lean_inc(v_messages_4172_);
                        lean_inc(v_traceState_4171_);
                        lean_inc(v_auxDeclNGen_4170_);
                        lean_inc(v_ngen_4169_);
                        lean_inc(v_nextMacroScope_4168_);
                        lean_inc(v_env_4167_);
                        lean_dec(v___x_4166_);
                        v___x_4176_ = lean_box(0);
                        v_isShared_4177_ = v_isSharedCheck_4184_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___y_4137_ = v___y_4158_;
                    v___y_4138_ = v___y_4160_;
                    v___y_4139_ = v___y_4161_;
                    v___y_4140_ = v___y_4162_;
                    v___y_4141_ = v___y_4164_;
                    v___y_4142_ = v___y_4163_;
                    v___y_4143_ = v___y_4159_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_4178_ = l_Lean_Kernel_enableDiag(v_env_4167_, v___y_4164_);
                v___x_4179_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__2_once),
                    _init_l_Lean_Elab_Tactic_evalImpossible___closed__2,
                );
                if v_isShared_4177_ == 0 {
                    lean_ctor_set(v___x_4176_, 5, v___x_4179_);
                    lean_ctor_set(v___x_4176_, 0, v___x_4178_);
                    v___x_4181_ = v___x_4176_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_4178_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_nextMacroScope_4168_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 2, v_ngen_4169_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 3, v_auxDeclNGen_4170_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 4, v_traceState_4171_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 5, v___x_4179_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 6, v_messages_4172_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 7, v_infoState_4173_);
                    lean_ctor_set(v_reuseFailAlloc_4183_, 8, v_snapshotTasks_4174_);
                    v___x_4181_ = v_reuseFailAlloc_4183_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_4182_ = lean_st_ref_set(v___y_4159_, v___x_4181_);
                v___y_4137_ = v___y_4158_;
                v___y_4138_ = v___y_4160_;
                v___y_4139_ = v___y_4161_;
                v___y_4140_ = v___y_4162_;
                v___y_4141_ = v___y_4164_;
                v___y_4142_ = v___y_4163_;
                v___y_4143_ = v___y_4159_;
                state = 8;
                continue;
            }
            12 => {
                v___x_4209_ = (lean_unbox(v_a_4188_) as u8);
                lean_dec(v_a_4188_);
                lean_inc(v_a_4190_);
                v___x_4210_ =
                    l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_mkImpossibleNegType(
                        v_a_4190_,
                        v_a_4193_,
                        v___x_4209_,
                        v___y_4205_,
                        v___y_4206_,
                        v___y_4207_,
                        v___y_4208_,
                    );
                if lean_obj_tag(v___x_4210_) == 0 {
                    v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
                    lean_inc(v_a_4211_);
                    lean_dec_ref_known(v___x_4210_, 1);
                    v_fst_4212_ = lean_ctor_get(v_a_4211_, 0);
                    v_snd_4213_ = lean_ctor_get(v_a_4211_, 1);
                    v_isSharedCheck_4320_ = (!lean_is_exclusive(v_a_4211_)) as u8;
                    if v_isSharedCheck_4320_ == 0 {
                        v___x_4215_ = v_a_4211_;
                        v_isShared_4216_ = v_isSharedCheck_4320_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_snd_4213_);
                        lean_inc(v_fst_4212_);
                        lean_dec(v_a_4211_);
                        v___x_4215_ = lean_box(0);
                        v_isShared_4216_ = v_isSharedCheck_4320_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_4199_);
                    lean_dec(v___x_4196_);
                    lean_dec(v_a_4190_);
                    v_a_4321_ = lean_ctor_get(v___x_4210_, 0);
                    v_isSharedCheck_4328_ = (!lean_is_exclusive(v___x_4210_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4323_ = v___x_4210_;
                        v_isShared_4324_ = v_isSharedCheck_4328_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_4321_);
                        lean_dec(v___x_4210_);
                        v___x_4323_ = lean_box(0);
                        v_isShared_4324_ = v_isSharedCheck_4328_;
                        state = 25;
                        continue;
                    }
                }
            }
            13 => {
                v___x_4217_ = l_Lean_Elab_admitGoal(
                    v_a_4190_,
                    v___x_4186_,
                    v___y_4205_,
                    v___y_4206_,
                    v___y_4207_,
                    v___y_4208_,
                );
                if lean_obj_tag(v___x_4217_) == 0 {
                    lean_dec_ref_known(v___x_4217_, 1);
                    v___x_4218_ = l_Lean_Elab_Tactic_getUnsolvedGoals(
                        v___y_4201_,
                        v___y_4202_,
                        v___y_4203_,
                        v___y_4204_,
                        v___y_4205_,
                        v___y_4206_,
                        v___y_4207_,
                        v___y_4208_,
                    );
                    if lean_obj_tag(v___x_4218_) == 0 {
                        v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
                        lean_inc(v_a_4219_);
                        lean_dec_ref_known(v___x_4218_, 1);
                        v___x_4220_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_evalImpossible___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_evalImpossible___closed__7_once
                            ),
                            _init_l_Lean_Elab_Tactic_evalImpossible___closed__7,
                        );
                        v___x_4221_ = l_Lean_Elab_Tactic_evalImpossible___closed__8;
                        v___x_4222_ = 2;
                        v___x_4223_ = lean_box(0);
                        lean_inc(v_fst_4212_);
                        v___x_4224_ = l_Lean_Meta_mkFreshExprMVarAt(
                            v___x_4220_,
                            v___x_4221_,
                            v_fst_4212_,
                            v___x_4222_,
                            v___x_4223_,
                            v___x_4194_,
                            v___y_4205_,
                            v___y_4206_,
                            v___y_4207_,
                            v___y_4208_,
                        );
                        if lean_obj_tag(v___x_4224_) == 0 {
                            v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
                            lean_inc(v_a_4225_);
                            lean_dec_ref_known(v___x_4224_, 1);
                            v___x_4226_ = l_Lean_Expr_mvarId_x21(v_a_4225_);
                            lean_dec(v_a_4225_);
                            v___x_4227_ = lean_array_get_size(v_snd_4213_);
                            v___x_4228_ = lean_array_to_list(v_snd_4213_);
                            lean_inc(v___x_4226_);
                            v___x_4229_ = l_Lean_Meta_introNCore(
                                v___x_4226_,
                                v___x_4227_,
                                v___x_4228_,
                                v___x_4111_,
                                v___x_4111_,
                                v___y_4205_,
                                v___y_4206_,
                                v___y_4207_,
                                v___y_4208_,
                            );
                            if lean_obj_tag(v___x_4229_) == 0 {
                                v_a_4230_ = lean_ctor_get(v___x_4229_, 0);
                                lean_inc(v_a_4230_);
                                lean_dec_ref_known(v___x_4229_, 1);
                                v_snd_4231_ = lean_ctor_get(v_a_4230_, 1);
                                v_isSharedCheck_4294_ = (!lean_is_exclusive(v_a_4230_)) as u8;
                                if v_isSharedCheck_4294_ == 0 {
                                    v_unused_4295_ = lean_ctor_get(v_a_4230_, 0);
                                    lean_dec(v_unused_4295_);
                                    v___x_4233_ = v_a_4230_;
                                    v_isShared_4234_ = v_isSharedCheck_4294_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_snd_4231_);
                                    lean_dec(v_a_4230_);
                                    v___x_4233_ = lean_box(0);
                                    v_isShared_4234_ = v_isSharedCheck_4294_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_4226_);
                                lean_dec(v_a_4219_);
                                lean_del_object(v___x_4215_);
                                lean_dec(v_fst_4212_);
                                lean_dec_ref(v___f_4199_);
                                lean_dec(v___x_4196_);
                                v_a_4296_ = lean_ctor_get(v___x_4229_, 0);
                                v_isSharedCheck_4303_ = (!lean_is_exclusive(v___x_4229_)) as u8;
                                if v_isSharedCheck_4303_ == 0 {
                                    v___x_4298_ = v___x_4229_;
                                    v_isShared_4299_ = v_isSharedCheck_4303_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_4296_);
                                    lean_dec(v___x_4229_);
                                    v___x_4298_ = lean_box(0);
                                    v_isShared_4299_ = v_isSharedCheck_4303_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_4219_);
                            lean_del_object(v___x_4215_);
                            lean_dec(v_snd_4213_);
                            lean_dec(v_fst_4212_);
                            lean_dec_ref(v___f_4199_);
                            lean_dec(v___x_4196_);
                            v_a_4304_ = lean_ctor_get(v___x_4224_, 0);
                            v_isSharedCheck_4311_ = (!lean_is_exclusive(v___x_4224_)) as u8;
                            if v_isSharedCheck_4311_ == 0 {
                                v___x_4306_ = v___x_4224_;
                                v_isShared_4307_ = v_isSharedCheck_4311_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_4304_);
                                lean_dec(v___x_4224_);
                                v___x_4306_ = lean_box(0);
                                v_isShared_4307_ = v_isSharedCheck_4311_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4215_);
                        lean_dec(v_snd_4213_);
                        lean_dec(v_fst_4212_);
                        lean_dec_ref(v___f_4199_);
                        lean_dec(v___x_4196_);
                        v_a_4312_ = lean_ctor_get(v___x_4218_, 0);
                        v_isSharedCheck_4319_ = (!lean_is_exclusive(v___x_4218_)) as u8;
                        if v_isSharedCheck_4319_ == 0 {
                            v___x_4314_ = v___x_4218_;
                            v_isShared_4315_ = v_isSharedCheck_4319_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_4312_);
                            lean_dec(v___x_4218_);
                            v___x_4314_ = lean_box(0);
                            v_isShared_4315_ = v_isSharedCheck_4319_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4215_);
                    lean_dec(v_snd_4213_);
                    lean_dec(v_fst_4212_);
                    lean_dec_ref(v___f_4199_);
                    lean_dec(v___x_4196_);
                    return v___x_4217_;
                }
            }
            14 => {
                v___x_4235_ = lean_box(0);
                if v_isShared_4234_ == 0 {
                    lean_ctor_set_tag(v___x_4233_, 1);
                    lean_ctor_set(v___x_4233_, 1, v___x_4235_);
                    lean_ctor_set(v___x_4233_, 0, v_snd_4231_);
                    v___x_4237_ = v___x_4233_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_snd_4231_);
                    lean_ctor_set(v_reuseFailAlloc_4293_, 1, v___x_4235_);
                    v___x_4237_ = v_reuseFailAlloc_4293_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_4238_ = l_Lean_Elab_Tactic_setGoals___redArg(v___x_4237_, v___y_4202_);
                if lean_obj_tag(v___x_4238_) == 0 {
                    lean_dec_ref_known(v___x_4238_, 1);
                    v___x_4239_ = l_Lean_Elab_Tactic_mkInitialTacticInfo(
                        v___x_4196_,
                        v___y_4201_,
                        v___y_4202_,
                        v___y_4203_,
                        v___y_4204_,
                        v___y_4205_,
                        v___y_4206_,
                        v___y_4207_,
                        v___y_4208_,
                    );
                    if lean_obj_tag(v___x_4239_) == 0 {
                        v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
                        lean_inc(v_a_4240_);
                        lean_dec_ref_known(v___x_4239_, 1);
                        v___f_4241_ = lean_alloc_closure(
                            l_Lean_Elab_Tactic_evalImpossible___lam__2___boxed
                                as *mut core::ffi::c_void,
                            11,
                            1,
                        );
                        lean_closure_set(v___f_4241_, 0, v_a_4240_);
                        v___x_4242_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(v___f_4199_, v___f_4241_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_);
                        if lean_obj_tag(v___x_4242_) == 0 {
                            lean_dec_ref_known(v___x_4242_, 1);
                            v___x_4243_ = l_Lean_mkMVar(v___x_4226_);
                            v___x_4244_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v___x_4243_, v___y_4206_);
                            v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
                            lean_inc(v_a_4245_);
                            lean_dec_ref(v___x_4244_);
                            v___x_4246_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_evalImpossible_spec__0___redArg(v_fst_4212_, v___y_4206_);
                            v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
                            lean_inc(v_a_4247_);
                            lean_dec_ref(v___x_4246_);
                            v___x_4248_ = l_Lean_Meta_Closure_mkValueTypeClosure(
                                v_a_4247_,
                                v_a_4245_,
                                v___x_4111_,
                                v___y_4205_,
                                v___y_4206_,
                                v___y_4207_,
                                v___y_4208_,
                            );
                            if lean_obj_tag(v___x_4248_) == 0 {
                                v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
                                lean_inc(v_a_4249_);
                                lean_dec_ref_known(v___x_4248_, 1);
                                v___x_4250_ = l_Lean_Elab_Tactic_evalImpossible___closed__10;
                                v___x_4251_ = l_Lean_mkAuxDeclName___at___00Lean_Elab_Tactic_evalImpossible_spec__3___redArg(v___x_4250_, v___y_4208_);
                                v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
                                v_isSharedCheck_4289_ = (!lean_is_exclusive(v___x_4251_)) as u8;
                                if v_isSharedCheck_4289_ == 0 {
                                    v___x_4254_ = v___x_4251_;
                                    v_isShared_4255_ = v_isSharedCheck_4289_;
                                    state = 16;
                                    continue;
                                } else {
                                    lean_inc(v_a_4252_);
                                    lean_dec(v___x_4251_);
                                    v___x_4254_ = lean_box(0);
                                    v_isShared_4255_ = v_isSharedCheck_4289_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_4215_);
                                v_a_4290_ = lean_ctor_get(v___x_4248_, 0);
                                lean_inc(v_a_4290_);
                                lean_dec_ref_known(v___x_4248_, 1);
                                v___y_4082_ = v_a_4219_;
                                v___y_4083_ = v___y_4202_;
                                v_a_4084_ = v_a_4290_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_4226_);
                            lean_del_object(v___x_4215_);
                            lean_dec(v_fst_4212_);
                            v_a_4291_ = lean_ctor_get(v___x_4242_, 0);
                            lean_inc(v_a_4291_);
                            lean_dec_ref_known(v___x_4242_, 1);
                            v___y_4082_ = v_a_4219_;
                            v___y_4083_ = v___y_4202_;
                            v_a_4084_ = v_a_4291_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_4226_);
                        lean_del_object(v___x_4215_);
                        lean_dec(v_fst_4212_);
                        lean_dec_ref(v___f_4199_);
                        v_a_4292_ = lean_ctor_get(v___x_4239_, 0);
                        lean_inc(v_a_4292_);
                        lean_dec_ref_known(v___x_4239_, 1);
                        v___y_4082_ = v_a_4219_;
                        v___y_4083_ = v___y_4202_;
                        v_a_4084_ = v_a_4292_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4226_);
                    lean_del_object(v___x_4215_);
                    lean_dec(v_fst_4212_);
                    lean_dec_ref(v___f_4199_);
                    lean_dec(v___x_4196_);
                    v___y_4095_ = v_a_4219_;
                    v___y_4096_ = v___y_4202_;
                    v___y_4097_ = v___x_4238_;
                    state = 4;
                    continue;
                }
            }
            16 => {
                v_levelParams_4256_ = lean_ctor_get(v_a_4249_, 0);
                lean_inc_ref(v_levelParams_4256_);
                v_type_4257_ = lean_ctor_get(v_a_4249_, 1);
                lean_inc_ref(v_type_4257_);
                v_value_4258_ = lean_ctor_get(v_a_4249_, 2);
                lean_inc_ref(v_value_4258_);
                lean_dec(v_a_4249_);
                v___x_4259_ = lean_st_ref_get(v___y_4208_);
                v_fileName_4260_ = lean_ctor_get(v___y_4207_, 0);
                v_fileMap_4261_ = lean_ctor_get(v___y_4207_, 1);
                v_options_4262_ = lean_ctor_get(v___y_4207_, 2);
                v_currRecDepth_4263_ = lean_ctor_get(v___y_4207_, 3);
                v_ref_4264_ = lean_ctor_get(v___y_4207_, 5);
                v_currNamespace_4265_ = lean_ctor_get(v___y_4207_, 6);
                v_openDecls_4266_ = lean_ctor_get(v___y_4207_, 7);
                v_initHeartbeats_4267_ = lean_ctor_get(v___y_4207_, 8);
                v_maxHeartbeats_4268_ = lean_ctor_get(v___y_4207_, 9);
                v_quotContext_4269_ = lean_ctor_get(v___y_4207_, 10);
                v_currMacroScope_4270_ = lean_ctor_get(v___y_4207_, 11);
                v_cancelTk_x3f_4271_ = lean_ctor_get(v___y_4207_, 12);
                v_suppressElabErrors_4272_ = lean_ctor_get_uint8(
                    v___y_4207_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4273_ = lean_ctor_get(v___y_4207_, 13);
                v_env_4274_ = lean_ctor_get(v___x_4259_, 0);
                lean_inc_ref(v_env_4274_);
                lean_dec(v___x_4259_);
                v___x_4275_ = lean_array_to_list(v_levelParams_4256_);
                lean_inc(v_a_4252_);
                v___x_4276_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4276_, 0, v_a_4252_);
                lean_ctor_set(v___x_4276_, 1, v___x_4275_);
                lean_ctor_set(v___x_4276_, 2, v_type_4257_);
                if v_isShared_4216_ == 0 {
                    lean_ctor_set_tag(v___x_4215_, 1);
                    lean_ctor_set(v___x_4215_, 1, v___x_4235_);
                    lean_ctor_set(v___x_4215_, 0, v_a_4252_);
                    v___x_4278_ = v___x_4215_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4252_);
                    lean_ctor_set(v_reuseFailAlloc_4288_, 1, v___x_4235_);
                    v___x_4278_ = v_reuseFailAlloc_4288_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_4279_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_4279_, 0, v___x_4276_);
                lean_ctor_set(v___x_4279_, 1, v_value_4258_);
                lean_ctor_set(v___x_4279_, 2, v___x_4278_);
                if v_isShared_4255_ == 0 {
                    lean_ctor_set_tag(v___x_4254_, 2);
                    lean_ctor_set(v___x_4254_, 0, v___x_4279_);
                    v___x_4281_ = v___x_4254_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4287_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4287_, 0, v___x_4279_);
                    v___x_4281_ = v_reuseFailAlloc_4287_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_4282_ = l_Lean_Elab_async;
                lean_inc_ref(v_options_4262_);
                v___x_4283_ = l_Lean_Option_set___at___00Lean_Elab_Tactic_evalImpossible_spec__4(
                    v_options_4262_,
                    v___x_4282_,
                    v___x_4111_,
                );
                v___x_4284_ = l_Lean_diagnostics;
                v___x_4285_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_elabImpossibleConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v___x_4283_, v___x_4284_);
                v___x_4286_ = l_Lean_Kernel_isDiagnosticsEnabled(v_env_4274_);
                lean_dec_ref(v_env_4274_);
                if v___x_4286_ == 0 {
                    if v___x_4285_ == 0 {
                        v___y_4113_ = v___x_4281_;
                        v___y_4114_ = v_a_4219_;
                        v___y_4115_ = v___x_4283_;
                        v___y_4116_ = v___y_4202_;
                        v___y_4117_ = v___x_4285_;
                        v_fileName_4118_ = v_fileName_4260_;
                        v_fileMap_4119_ = v_fileMap_4261_;
                        v_currRecDepth_4120_ = v_currRecDepth_4263_;
                        v_ref_4121_ = v_ref_4264_;
                        v_currNamespace_4122_ = v_currNamespace_4265_;
                        v_openDecls_4123_ = v_openDecls_4266_;
                        v_initHeartbeats_4124_ = v_initHeartbeats_4267_;
                        v_maxHeartbeats_4125_ = v_maxHeartbeats_4268_;
                        v_quotContext_4126_ = v_quotContext_4269_;
                        v_currMacroScope_4127_ = v_currMacroScope_4270_;
                        v_cancelTk_x3f_4128_ = v_cancelTk_x3f_4271_;
                        v_suppressElabErrors_4129_ = v_suppressElabErrors_4272_;
                        v_inheritedTraceOptions_4130_ = v_inheritedTraceOptions_4273_;
                        v___y_4131_ = v___y_4208_;
                        state = 7;
                        continue;
                    } else {
                        v___y_4158_ = v___x_4281_;
                        v___y_4159_ = v___y_4208_;
                        v___y_4160_ = v_a_4219_;
                        v___y_4161_ = v___x_4283_;
                        v___y_4162_ = v___y_4202_;
                        v___y_4163_ = v___y_4207_;
                        v___y_4164_ = v___x_4285_;
                        v___y_4165_ = v___x_4286_;
                        state = 9;
                        continue;
                    }
                } else {
                    v___y_4158_ = v___x_4281_;
                    v___y_4159_ = v___y_4208_;
                    v___y_4160_ = v_a_4219_;
                    v___y_4161_ = v___x_4283_;
                    v___y_4162_ = v___y_4202_;
                    v___y_4163_ = v___y_4207_;
                    v___y_4164_ = v___x_4285_;
                    v___y_4165_ = v___x_4285_;
                    state = 9;
                    continue;
                }
            }
            19 => {
                if v_isShared_4299_ == 0 {
                    v___x_4301_ = v___x_4298_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4302_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4302_, 0, v_a_4296_);
                    v___x_4301_ = v_reuseFailAlloc_4302_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4301_;
            }
            21 => {
                if v_isShared_4307_ == 0 {
                    v___x_4309_ = v___x_4306_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
                    v___x_4309_ = v_reuseFailAlloc_4310_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4309_;
            }
            23 => {
                if v_isShared_4315_ == 0 {
                    v___x_4317_ = v___x_4314_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
                    v___x_4317_ = v_reuseFailAlloc_4318_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4317_;
            }
            25 => {
                if v_isShared_4324_ == 0 {
                    v___x_4326_ = v___x_4323_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
                    v___x_4326_ = v_reuseFailAlloc_4327_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4326_;
            }
            27 => {
                if v_isShared_4338_ == 0 {
                    v___x_4340_ = v___x_4337_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4341_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_a_4335_);
                    v___x_4340_ = v_reuseFailAlloc_4341_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4340_;
            }
            29 => {
                if v_isShared_4346_ == 0 {
                    v___x_4348_ = v___x_4345_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
                    v___x_4348_ = v_reuseFailAlloc_4349_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4348_;
            }
            31 => {
                if v_isShared_4354_ == 0 {
                    v___x_4356_ = v___x_4353_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
                    v___x_4356_ = v_reuseFailAlloc_4357_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_4356_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalImpossible___boxed(
    mut v_stx_4359_: *mut LeanObject,
    mut v_a_4360_: *mut LeanObject,
    mut v_a_4361_: *mut LeanObject,
    mut v_a_4362_: *mut LeanObject,
    mut v_a_4363_: *mut LeanObject,
    mut v_a_4364_: *mut LeanObject,
    mut v_a_4365_: *mut LeanObject,
    mut v_a_4366_: *mut LeanObject,
    mut v_a_4367_: *mut LeanObject,
    mut v_a_4368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4369_: *mut LeanObject = core::ptr::null_mut();
    v_res_4369_ = l_Lean_Elab_Tactic_evalImpossible(
        v_stx_4359_,
        v_a_4360_,
        v_a_4361_,
        v_a_4362_,
        v_a_4363_,
        v_a_4364_,
        v_a_4365_,
        v_a_4366_,
        v_a_4367_,
    );
    lean_dec(v_a_4367_);
    lean_dec_ref(v_a_4366_);
    lean_dec(v_a_4365_);
    lean_dec_ref(v_a_4364_);
    lean_dec(v_a_4363_);
    lean_dec_ref(v_a_4362_);
    lean_dec(v_a_4361_);
    lean_dec_ref(v_a_4360_);
    lean_dec(v_stx_4359_);
    return v_res_4369_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(
    mut v___y_4370_: *mut LeanObject,
    mut v___y_4371_: *mut LeanObject,
    mut v___y_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4379_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___redArg(v___y_4377_);
    return v___x_4379_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2___boxed(
    mut v___y_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
    mut v___y_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
    mut v___y_4387_: *mut LeanObject,
    mut v___y_4388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4389_: *mut LeanObject = core::ptr::null_mut();
    v_res_4389_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2_spec__2(v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
    lean_dec(v___y_4387_);
    lean_dec_ref(v___y_4386_);
    lean_dec(v___y_4385_);
    lean_dec_ref(v___y_4384_);
    lean_dec(v___y_4383_);
    lean_dec_ref(v___y_4382_);
    lean_dec(v___y_4381_);
    lean_dec_ref(v___y_4380_);
    return v_res_4389_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(
    mut v_00_u03b1_4390_: *mut LeanObject,
    mut v_x_4391_: *mut LeanObject,
    mut v_mkInfoTree_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    v___x_4402_ =
        l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___redArg(
            v_x_4391_,
            v_mkInfoTree_4392_,
            v___y_4393_,
            v___y_4394_,
            v___y_4395_,
            v___y_4396_,
            v___y_4397_,
            v___y_4398_,
            v___y_4399_,
            v___y_4400_,
        );
    return v___x_4402_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2___boxed(
    mut v_00_u03b1_4403_: *mut LeanObject,
    mut v_x_4404_: *mut LeanObject,
    mut v_mkInfoTree_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
    mut v___y_4410_: *mut LeanObject,
    mut v___y_4411_: *mut LeanObject,
    mut v___y_4412_: *mut LeanObject,
    mut v___y_4413_: *mut LeanObject,
    mut v___y_4414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4415_: *mut LeanObject = core::ptr::null_mut();
    v_res_4415_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_Tactic_evalImpossible_spec__2(
        v_00_u03b1_4403_,
        v_x_4404_,
        v_mkInfoTree_4405_,
        v___y_4406_,
        v___y_4407_,
        v___y_4408_,
        v___y_4409_,
        v___y_4410_,
        v___y_4411_,
        v___y_4412_,
        v___y_4413_,
    );
    lean_dec(v___y_4413_);
    lean_dec_ref(v___y_4412_);
    lean_dec(v___y_4411_);
    lean_dec_ref(v___y_4410_);
    lean_dec(v___y_4409_);
    lean_dec_ref(v___y_4408_);
    lean_dec(v___y_4407_);
    lean_dec_ref(v___y_4406_);
    return v_res_4415_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(
    mut v_00_u03b1_4416_: *mut LeanObject,
    mut v_ref_4417_: *mut LeanObject,
    mut v_msg_4418_: *mut LeanObject,
    mut v___y_4419_: *mut LeanObject,
    mut v___y_4420_: *mut LeanObject,
    mut v___y_4421_: *mut LeanObject,
    mut v___y_4422_: *mut LeanObject,
    mut v___y_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
    mut v___y_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    v___x_4428_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___redArg(
        v_ref_4417_,
        v_msg_4418_,
        v___y_4419_,
        v___y_4420_,
        v___y_4421_,
        v___y_4422_,
        v___y_4423_,
        v___y_4424_,
        v___y_4425_,
        v___y_4426_,
    );
    return v___x_4428_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6___boxed(
    mut v_00_u03b1_4429_: *mut LeanObject,
    mut v_ref_4430_: *mut LeanObject,
    mut v_msg_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
    mut v___y_4435_: *mut LeanObject,
    mut v___y_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
    mut v___y_4439_: *mut LeanObject,
    mut v___y_4440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4441_: *mut LeanObject = core::ptr::null_mut();
    v_res_4441_ = l_Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6(
        v_00_u03b1_4429_,
        v_ref_4430_,
        v_msg_4431_,
        v___y_4432_,
        v___y_4433_,
        v___y_4434_,
        v___y_4435_,
        v___y_4436_,
        v___y_4437_,
        v___y_4438_,
        v___y_4439_,
    );
    lean_dec(v___y_4439_);
    lean_dec_ref(v___y_4438_);
    lean_dec(v___y_4437_);
    lean_dec_ref(v___y_4436_);
    lean_dec(v___y_4435_);
    lean_dec_ref(v___y_4434_);
    lean_dec(v___y_4433_);
    lean_dec_ref(v___y_4432_);
    lean_dec(v_ref_4430_);
    return v_res_4441_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(
    mut v_00_u03b1_4442_: *mut LeanObject,
    mut v_msg_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
    mut v___y_4446_: *mut LeanObject,
    mut v___y_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    v___x_4453_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___redArg(v_msg_4443_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
    return v___x_4453_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8___boxed(
    mut v_00_u03b1_4454_: *mut LeanObject,
    mut v_msg_4455_: *mut LeanObject,
    mut v___y_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
    mut v___y_4459_: *mut LeanObject,
    mut v___y_4460_: *mut LeanObject,
    mut v___y_4461_: *mut LeanObject,
    mut v___y_4462_: *mut LeanObject,
    mut v___y_4463_: *mut LeanObject,
    mut v___y_4464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4465_: *mut LeanObject = core::ptr::null_mut();
    v_res_4465_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Tactic_evalImpossible_spec__6_spec__8(v_00_u03b1_4454_, v_msg_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
    lean_dec(v___y_4463_);
    lean_dec_ref(v___y_4462_);
    lean_dec(v___y_4461_);
    lean_dec_ref(v___y_4460_);
    lean_dec(v___y_4459_);
    lean_dec_ref(v___y_4458_);
    lean_dec(v___y_4457_);
    lean_dec_ref(v___y_4456_);
    return v_res_4465_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1()
-> *mut LeanObject {
    let mut v___x_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    v___x_4480_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_4481_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__1;
    v___x_4482_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___closed__4;
    v___x_4483_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_evalImpossible___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_4484_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4480_,
        v___x_4481_,
        v___x_4482_,
        v___x_4483_,
    );
    return v___x_4484_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1___boxed(
    mut v_a_4485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4486_: *mut LeanObject = core::ptr::null_mut();
    v_res_4486_ = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1();
    return v_res_4486_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Impossible(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig = _init_l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig();
    lean_mark_persistent(
        l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_instEvalExprImpossibleConfig,
    );
    res = l___private_Lean_Elab_Tactic_Impossible_0__Lean_Elab_Tactic_evalImpossible___regBuiltin_Lean_Elab_Tactic_evalImpossible__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Impossible(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Impossible(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Elab_ConfigEval(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cleanup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Revert(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Closure(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Impossible(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Impossible(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Impossible(builtin);
}
