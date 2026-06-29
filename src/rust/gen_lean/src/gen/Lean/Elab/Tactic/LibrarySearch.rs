// Lean compiler output
// Module: Lean.Elab.Tactic.LibrarySearch
// Imports: Lean.Meta.Tactic.LibrarySearch Lean.Meta.Tactic.TryThis Lean.Elab.Tactic.ElabTerm Lean.Elab.ConfigEval
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_of_nat,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
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
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_saveState___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute, l_Lean_Elab_admitGoal,
};
use crate::r#gen::Lean::Elab::Tactic::ElabTerm::{
    initialize_Lean_Elab_Tactic_ElabTerm, l_Lean_Elab_Tactic_getFVarId,
    runtime_initialize_Lean_Elab_Tactic_ElabTerm,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTermEnsuringType___boxed, l_Lean_Elab_Term_logUnassignedUsingErrorInfos,
    l_Lean_Elab_Term_termElabAttribute, l_Lean_Elab_Term_withExpectedType,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_fvar___override, l_Lean_Expr_hasMVar,
    l_Lean_Expr_headBeta, l_Lean_Expr_mvar___override, l_Lean_Expr_mvarId_x21,
    l_Lean_instInhabitedExpr, l_Lean_mkConst, l_Lean_mkMVar,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVars;
use crate::r#gen::Lean::Meta::Sorry::l_Lean_Meta_mkLabeledSorry;
use crate::r#gen::Lean::Meta::Tactic::Intro::l_Lean_MVarId_intros;
use crate::r#gen::Lean::Meta::Tactic::LibrarySearch::{
    initialize_Lean_Meta_Tactic_LibrarySearch, l_Lean_Meta_LibrarySearch_librarySearch,
    l_Lean_Meta_LibrarySearch_solveByElim, runtime_initialize_Lean_Meta_Tactic_LibrarySearch,
};
use crate::r#gen::Lean::Meta::Tactic::TryThis::{
    initialize_Lean_Meta_Tactic_TryThis, l_Lean_Meta_Tactic_TryThis_addExactSuggestion,
    l_Lean_Meta_Tactic_TryThis_addExactSuggestions, l_Lean_Meta_Tactic_TryThis_addTermSuggestion,
    runtime_initialize_Lean_Meta_Tactic_TryThis,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Util::FindExpr::l_Lean_Expr_occurs;
use crate::r#gen::Lean::Util::Heartbeats::l_Lean_reportOutOfHeartbeats;
use crate::r#gen::Lean::Util::Sorry::{l_Lean_Expr_hasSorry, l_Lean_Expr_hasSyntheticSorry};
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [76, 105, 98, 114, 97, 114, 121, 83, 101, 97, 114, 99, 104, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut crate::leanh::LeanObject,9896841084116499507 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 96, 115, 111, 114, 114, 121, 96, 58, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__0_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 97, 114, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 121, 63, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut crate::leanh::LeanObject,9896841084116499507 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,15737842007922976103 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut crate::leanh::LeanObject,9896841084116499507 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,1745771790535957399 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut crate::leanh::LeanObject,9896841084116499507 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,11983762874465944583 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut crate::leanh::LeanObject,9896841084116499507 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,16400000088529102175 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value:
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
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        97, 112, 112, 108, 121, 63, 32, 100, 105, 100, 110, 39, 116, 32, 102, 105, 110, 100, 32,
        97, 110, 121, 32, 114, 101, 108, 101, 118, 97, 110, 116, 32, 108, 101, 109, 109, 97, 115,
        0,
    ],
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value:
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
    m_data: [97, 112, 112, 108, 121, 63, 0],
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value)
            as *mut crate::leanh::LeanObject,
        5070879632462810678 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        96, 101, 120, 97, 99, 116, 63, 96, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 99,
        108, 111, 115, 101, 32, 116, 104, 101, 32, 103, 111, 97, 108, 46, 0,
    ],
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        32, 84, 114, 121, 32, 96, 97, 112, 112, 108, 121, 63, 96, 32, 116, 111, 32, 115, 101, 101,
        32, 112, 97, 114, 116, 105, 97, 108, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110,
        115, 46, 0,
    ],
};
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__0_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 120, 97, 99, 116, 63, 0],
};
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__0_value)
                as *mut crate::leanh::LeanObject,
            5826269145198601482 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__2_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
};
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__2_value)
                as *mut crate::leanh::LeanObject,
            3488656302031949961 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__4_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 105, 98, 114, 97, 114, 121, 83, 101, 97, 114, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 69, 120, 97, 99, 116, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut crate::leanh::LeanObject,17680530212324118304 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1_value) as *mut crate::leanh::LeanObject,11860042555288360565 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 33 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value)
                as *mut crate::leanh::LeanObject,
            16444823490062833535 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_evalApply___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 65, 112, 112, 108, 121, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut crate::leanh::LeanObject,17680530212324118304 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0_value) as *mut crate::leanh::LeanObject,559802866465757943 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 61 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 34 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0_value:
    crate::leanh::LeanStringObject<80> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 80,
    m_capacity: 80,
    m_length: 79,
    m_data: [
        96, 101, 120, 97, 99, 116, 63, 37, 96, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32,
        99, 108, 111, 115, 101, 32, 116, 104, 101, 32, 103, 111, 97, 108, 46, 32, 84, 114, 121, 32,
        96, 98, 121, 32, 97, 112, 112, 108, 121, 63, 96, 32, 116, 111, 32, 115, 101, 101, 32, 112,
        97, 114, 116, 105, 97, 108, 32, 115, 117, 103, 103, 101, 115, 116, 105, 111, 110, 115, 46,
        0,
    ],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        96, 101, 120, 97, 99, 116, 63, 37, 96, 32, 100, 105, 100, 110, 39, 116, 32, 102, 105, 110,
        100, 32, 97, 110, 121, 32, 114, 101, 108, 101, 118, 97, 110, 116, 32, 108, 101, 109, 109,
        97, 115, 0,
    ],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__6_value:
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
    m_data: [84, 114, 121, 32, 116, 104, 105, 115, 58, 0],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0_value:
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
    m_data: [83, 121, 110, 116, 97, 120, 0],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1765827125244227832 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11838310352122951404 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 69, 120, 97, 99, 116, 63, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut crate::leanh::LeanObject,17680530212324118304 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0_value) as *mut crate::leanh::LeanObject,1366678009817496993 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 76 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 29 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 29 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 18 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 18 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3131_ = crate::leanh::lean_box(0);
    v___x_3132_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_3133_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3133_, 0, v___x_3132_);
    crate::leanh::lean_ctor_set(v___x_3133_, 1, v___x_3131_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3135_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0);
    v___x_3136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3136_, 0, v___x_3135_);
    return v___x_3136_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___boxed(
    mut v___y_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3138_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg();
    return v_res_3138_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0(
    mut v_00_u03b1_3139_: *mut crate::leanh::LeanObject,
    mut v___y_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3145_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg();
    return v___x_3145_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___boxed(
    mut v_00_u03b1_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0(v_00_u03b1_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
    crate::leanh::lean_dec(v___y_3150_);
    crate::leanh::lean_dec_ref(v___y_3149_);
    crate::leanh::lean_dec(v___y_3148_);
    crate::leanh::lean_dec_ref(v___y_3147_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(
    mut v_msgData_3153_: *mut crate::leanh::LeanObject,
    mut v___y_3154_: *mut crate::leanh::LeanObject,
    mut v___y_3155_: *mut crate::leanh::LeanObject,
    mut v___y_3156_: *mut crate::leanh::LeanObject,
    mut v___y_3157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3159_ = lean_st_ref_get(v___y_3157_);
    v_env_3160_ = crate::leanh::lean_ctor_get(v___x_3159_, 0);
    crate::leanh::lean_inc_ref(v_env_3160_);
    crate::leanh::lean_dec(v___x_3159_);
    v___x_3161_ = lean_st_ref_get(v___y_3155_);
    v_mctx_3162_ = crate::leanh::lean_ctor_get(v___x_3161_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3162_);
    crate::leanh::lean_dec(v___x_3161_);
    v_lctx_3163_ = crate::leanh::lean_ctor_get(v___y_3154_, 2);
    v_options_3164_ = crate::leanh::lean_ctor_get(v___y_3156_, 2);
    crate::leanh::lean_inc_ref(v_options_3164_);
    crate::leanh::lean_inc_ref(v_lctx_3163_);
    v___x_3165_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3165_, 0, v_env_3160_);
    crate::leanh::lean_ctor_set(v___x_3165_, 1, v_mctx_3162_);
    crate::leanh::lean_ctor_set(v___x_3165_, 2, v_lctx_3163_);
    crate::leanh::lean_ctor_set(v___x_3165_, 3, v_options_3164_);
    v___x_3166_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3166_, 0, v___x_3165_);
    crate::leanh::lean_ctor_set(v___x_3166_, 1, v_msgData_3153_);
    v___x_3167_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3167_, 0, v___x_3166_);
    return v___x_3167_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1___boxed(
    mut v_msgData_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
    mut v___y_3173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msgData_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
    crate::leanh::lean_dec(v___y_3172_);
    crate::leanh::lean_dec_ref(v___y_3171_);
    crate::leanh::lean_dec(v___y_3170_);
    crate::leanh::lean_dec_ref(v___y_3169_);
    return v_res_3174_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(
    mut v_msg_3175_: *mut crate::leanh::LeanObject,
    mut v___y_3176_: *mut crate::leanh::LeanObject,
    mut v___y_3177_: *mut crate::leanh::LeanObject,
    mut v___y_3178_: *mut crate::leanh::LeanObject,
    mut v___y_3179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3181_ = crate::leanh::lean_ctor_get(v___y_3178_, 5);
                v___x_3182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msg_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
                v_a_3183_ = crate::leanh::lean_ctor_get(v___x_3182_, 0);
                v_isSharedCheck_3191_ = (!crate::leanh::lean_is_exclusive(v___x_3182_)) as u8;
                if v_isSharedCheck_3191_ == 0 {
                    v___x_3185_ = v___x_3182_;
                    v_isShared_3186_ = v_isSharedCheck_3191_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3183_);
                    crate::leanh::lean_dec(v___x_3182_);
                    v___x_3185_ = crate::leanh::lean_box(0);
                    v_isShared_3186_ = v_isSharedCheck_3191_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3181_);
                v___x_3187_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3187_, 0, v_ref_3181_);
                crate::leanh::lean_ctor_set(v___x_3187_, 1, v_a_3183_);
                if v_isShared_3186_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3185_, 1);
                    crate::leanh::lean_ctor_set(v___x_3185_, 0, v___x_3187_);
                    v___x_3189_ = v___x_3185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
                    v___x_3189_ = v_reuseFailAlloc_3190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg___boxed(
    mut v_msg_3192_: *mut crate::leanh::LeanObject,
    mut v___y_3193_: *mut crate::leanh::LeanObject,
    mut v___y_3194_: *mut crate::leanh::LeanObject,
    mut v___y_3195_: *mut crate::leanh::LeanObject,
    mut v___y_3196_: *mut crate::leanh::LeanObject,
    mut v___y_3197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(v_msg_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
    crate::leanh::lean_dec(v___y_3196_);
    crate::leanh::lean_dec_ref(v___y_3195_);
    crate::leanh::lean_dec(v___y_3194_);
    crate::leanh::lean_dec_ref(v___y_3193_);
    return v_res_3198_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3201_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1;
    v___x_3202_ = l_Lean_stringToMessageData(v___x_3201_);
    return v___x_3202_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0(
    mut v_ctor_3203_: *mut crate::leanh::LeanObject,
    mut v_args_3204_: *mut crate::leanh::LeanObject,
    mut v___y_3205_: *mut crate::leanh::LeanObject,
    mut v___y_3206_: *mut crate::leanh::LeanObject,
    mut v___y_3207_: *mut crate::leanh::LeanObject,
    mut v___y_3208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: u8 = 0;
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_a_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_a_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_a_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_a_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: u8 = 0;
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3272_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__0;
                v___x_3273_ = lean_string_dec_eq(v_ctor_3203_, v___x_3272_);
                if v___x_3273_ == 0 {
                    v___x_3274_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg();
                    return v___x_3274_;
                } else {
                    v___x_3275_ = lean_array_get_size(v_args_3204_);
                    v___x_3276_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3277_ = lean_nat_dec_eq(v___x_3275_, v___x_3276_);
                    if v___x_3277_ == 0 {
                        v___x_3278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2);
                        v___x_3279_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(v___x_3278_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
                        v_a_3280_ = crate::leanh::lean_ctor_get(v___x_3279_, 0);
                        v_isSharedCheck_3287_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3279_)) as u8;
                        if v_isSharedCheck_3287_ == 0 {
                            v___x_3282_ = v___x_3279_;
                            v_isShared_3283_ = v_isSharedCheck_3287_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3280_);
                            crate::leanh::lean_dec(v___x_3279_);
                            v___x_3282_ = crate::leanh::lean_box(0);
                            v_isShared_3283_ = v_isSharedCheck_3287_;
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
                v___x_3211_ = l_Lean_instInhabitedExpr;
                v___x_3212_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3213_ = lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3212_);
                crate::leanh::lean_inc(v___x_3213_);
                v___x_3214_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                    v___x_3213_,
                    v___y_3205_,
                    v___y_3206_,
                    v___y_3207_,
                    v___y_3208_,
                );
                if crate::leanh::lean_obj_tag(v___x_3214_) == 0 {
                    v_a_3215_ = crate::leanh::lean_ctor_get(v___x_3214_, 0);
                    crate::leanh::lean_inc(v_a_3215_);
                    crate::leanh::lean_dec_ref_known(v___x_3214_, 1);
                    v___x_3216_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3217_ = lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3216_);
                    crate::leanh::lean_inc(v___x_3217_);
                    v___x_3218_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                        v___x_3217_,
                        v___y_3205_,
                        v___y_3206_,
                        v___y_3207_,
                        v___y_3208_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3218_) == 0 {
                        v_a_3219_ = crate::leanh::lean_ctor_get(v___x_3218_, 0);
                        crate::leanh::lean_inc(v_a_3219_);
                        crate::leanh::lean_dec_ref_known(v___x_3218_, 1);
                        v___x_3220_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3221_ =
                            lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3220_);
                        crate::leanh::lean_inc(v___x_3221_);
                        v___x_3222_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                            v___x_3221_,
                            v___y_3205_,
                            v___y_3206_,
                            v___y_3207_,
                            v___y_3208_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3222_) == 0 {
                            v_a_3223_ = crate::leanh::lean_ctor_get(v___x_3222_, 0);
                            crate::leanh::lean_inc(v_a_3223_);
                            crate::leanh::lean_dec_ref_known(v___x_3222_, 1);
                            v___x_3224_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_3225_ =
                                lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3224_);
                            crate::leanh::lean_inc(v___x_3225_);
                            v___x_3226_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                v___x_3225_,
                                v___y_3205_,
                                v___y_3206_,
                                v___y_3207_,
                                v___y_3208_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3226_) == 0 {
                                v_a_3227_ = crate::leanh::lean_ctor_get(v___x_3226_, 0);
                                v_isSharedCheck_3239_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3226_)) as u8;
                                if v_isSharedCheck_3239_ == 0 {
                                    v___x_3229_ = v___x_3226_;
                                    v_isShared_3230_ = v_isSharedCheck_3239_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3227_);
                                    crate::leanh::lean_dec(v___x_3226_);
                                    v___x_3229_ = crate::leanh::lean_box(0);
                                    v_isShared_3230_ = v_isSharedCheck_3239_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3223_);
                                crate::leanh::lean_dec(v_a_3219_);
                                crate::leanh::lean_dec(v_a_3215_);
                                v_a_3240_ = crate::leanh::lean_ctor_get(v___x_3226_, 0);
                                v_isSharedCheck_3247_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3226_)) as u8;
                                if v_isSharedCheck_3247_ == 0 {
                                    v___x_3242_ = v___x_3226_;
                                    v_isShared_3243_ = v_isSharedCheck_3247_;
                                    state = 4;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3240_);
                                    crate::leanh::lean_dec(v___x_3226_);
                                    v___x_3242_ = crate::leanh::lean_box(0);
                                    v_isShared_3243_ = v_isSharedCheck_3247_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3219_);
                            crate::leanh::lean_dec(v_a_3215_);
                            v_a_3248_ = crate::leanh::lean_ctor_get(v___x_3222_, 0);
                            v_isSharedCheck_3255_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3222_)) as u8;
                            if v_isSharedCheck_3255_ == 0 {
                                v___x_3250_ = v___x_3222_;
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3248_);
                                crate::leanh::lean_dec(v___x_3222_);
                                v___x_3250_ = crate::leanh::lean_box(0);
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3215_);
                        v_a_3256_ = crate::leanh::lean_ctor_get(v___x_3218_, 0);
                        v_isSharedCheck_3263_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3218_)) as u8;
                        if v_isSharedCheck_3263_ == 0 {
                            v___x_3258_ = v___x_3218_;
                            v_isShared_3259_ = v_isSharedCheck_3263_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3256_);
                            crate::leanh::lean_dec(v___x_3218_);
                            v___x_3258_ = crate::leanh::lean_box(0);
                            v_isShared_3259_ = v_isSharedCheck_3263_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_3264_ = crate::leanh::lean_ctor_get(v___x_3214_, 0);
                    v_isSharedCheck_3271_ = (!crate::leanh::lean_is_exclusive(v___x_3214_)) as u8;
                    if v_isSharedCheck_3271_ == 0 {
                        v___x_3266_ = v___x_3214_;
                        v_isShared_3267_ = v_isSharedCheck_3271_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3264_);
                        crate::leanh::lean_dec(v___x_3214_);
                        v___x_3266_ = crate::leanh::lean_box(0);
                        v_isShared_3267_ = v_isSharedCheck_3271_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3231_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                v___x_3232_ = (crate::leanh::lean_unbox(v_a_3215_) as u8);
                crate::leanh::lean_dec(v_a_3215_);
                crate::leanh::lean_ctor_set_uint8(v___x_3231_, 0 as u32, v___x_3232_);
                v___x_3233_ = (crate::leanh::lean_unbox(v_a_3219_) as u8);
                crate::leanh::lean_dec(v_a_3219_);
                crate::leanh::lean_ctor_set_uint8(v___x_3231_, 1 as u32, v___x_3233_);
                v___x_3234_ = (crate::leanh::lean_unbox(v_a_3223_) as u8);
                crate::leanh::lean_dec(v_a_3223_);
                crate::leanh::lean_ctor_set_uint8(v___x_3231_, 2 as u32, v___x_3234_);
                v___x_3235_ = (crate::leanh::lean_unbox(v_a_3227_) as u8);
                crate::leanh::lean_dec(v_a_3227_);
                crate::leanh::lean_ctor_set_uint8(v___x_3231_, 3 as u32, v___x_3235_);
                if v_isShared_3230_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3229_, 0, v___x_3231_);
                    v___x_3237_ = v___x_3229_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3231_);
                    v___x_3237_ = v_reuseFailAlloc_3238_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3237_;
            }
            4 => {
                if v_isShared_3243_ == 0 {
                    v___x_3245_ = v___x_3242_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
                    v___x_3245_ = v_reuseFailAlloc_3246_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3245_;
            }
            6 => {
                if v_isShared_3251_ == 0 {
                    v___x_3253_ = v___x_3250_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
                    v___x_3253_ = v_reuseFailAlloc_3254_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3253_;
            }
            8 => {
                if v_isShared_3259_ == 0 {
                    v___x_3261_ = v___x_3258_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3261_;
            }
            10 => {
                if v_isShared_3267_ == 0 {
                    v___x_3269_ = v___x_3266_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3270_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
                    v___x_3269_ = v_reuseFailAlloc_3270_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3269_;
            }
            12 => {
                if v_isShared_3283_ == 0 {
                    v___x_3285_ = v___x_3282_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
                    v___x_3285_ = v_reuseFailAlloc_3286_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___boxed(
    mut v_ctor_3288_: *mut crate::leanh::LeanObject,
    mut v_args_3289_: *mut crate::leanh::LeanObject,
    mut v___y_3290_: *mut crate::leanh::LeanObject,
    mut v___y_3291_: *mut crate::leanh::LeanObject,
    mut v___y_3292_: *mut crate::leanh::LeanObject,
    mut v___y_3293_: *mut crate::leanh::LeanObject,
    mut v___y_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3295_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0(v_ctor_3288_, v_args_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
    crate::leanh::lean_dec(v___y_3293_);
    crate::leanh::lean_dec_ref(v___y_3292_);
    crate::leanh::lean_dec(v___y_3291_);
    crate::leanh::lean_dec_ref(v___y_3290_);
    crate::leanh::lean_dec_ref(v_args_3289_);
    crate::leanh::lean_dec_ref(v_ctor_3288_);
    return v_res_3295_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr(
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3312_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__0;
    v___x_3313_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5;
    v___x_3314_ = l_Lean_Elab_ConfigEval_EvalExpr_withSimpleEvalExpr___redArg(
        v___x_3313_,
        v___f_3312_,
        v_a_3306_,
        v_a_3307_,
        v_a_3308_,
        v_a_3309_,
        v_a_3310_,
    );
    return v___x_3314_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___boxed(
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
    mut v_a_3320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3321_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr(v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
    crate::leanh::lean_dec(v_a_3319_);
    crate::leanh::lean_dec_ref(v_a_3318_);
    crate::leanh::lean_dec(v_a_3317_);
    crate::leanh::lean_dec_ref(v_a_3316_);
    return v_res_3321_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1(
    mut v_00_u03b1_3322_: *mut crate::leanh::LeanObject,
    mut v_msg_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
    mut v___y_3325_: *mut crate::leanh::LeanObject,
    mut v___y_3326_: *mut crate::leanh::LeanObject,
    mut v___y_3327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3329_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(v_msg_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
    return v___x_3329_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___boxed(
    mut v_00_u03b1_3330_: *mut crate::leanh::LeanObject,
    mut v_msg_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
    mut v___y_3336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1(v_00_u03b1_3330_, v_msg_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
    crate::leanh::lean_dec(v___y_3335_);
    crate::leanh::lean_dec_ref(v___y_3334_);
    crate::leanh::lean_dec(v___y_3333_);
    crate::leanh::lean_dec_ref(v___y_3332_);
    return v_res_3337_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = crate::leanh::lean_box(0);
    v___x_3340_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5;
    v___x_3341_ = l_Lean_Expr_const___override(v___x_3340_, v___x_3339_);
    return v___x_3341_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1);
    v___x_3343_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3343_, 0, v___x_3342_);
    return v___x_3343_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3344_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2);
    v___x_3345_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0;
    v___x_3346_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3346_, 0, v___x_3345_);
    crate::leanh::lean_ctor_set(v___x_3346_, 1, v___x_3344_);
    return v___x_3346_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3);
    return v___x_3347_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(
    mut v_opts_3348_: *mut crate::leanh::LeanObject,
    mut v_opt_3349_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3350_ = crate::leanh::lean_ctor_get(v_opt_3349_, 0);
    v_defValue_3351_ = crate::leanh::lean_ctor_get(v_opt_3349_, 1);
    v_map_3352_ = crate::leanh::lean_ctor_get(v_opts_3348_, 0);
    v___x_3353_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3352_,
            v_name_3350_,
        );
    if crate::leanh::lean_obj_tag(v___x_3353_) == 0 {
        let mut v___x_3354_: u8 = 0;
        v___x_3354_ = (crate::leanh::lean_unbox(v_defValue_3351_) as u8);
        return v___x_3354_;
    } else {
        let mut v_val_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3355_ = crate::leanh::lean_ctor_get(v___x_3353_, 0);
        crate::leanh::lean_inc(v_val_3355_);
        crate::leanh::lean_dec_ref_known(v___x_3353_, 1);
        if crate::leanh::lean_obj_tag(v_val_3355_) == 1 {
            let mut v_v_3356_: u8 = 0;
            v_v_3356_ = crate::leanh::lean_ctor_get_uint8(v_val_3355_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3355_, 0);
            return v_v_3356_;
        } else {
            let mut v___x_3357_: u8 = 0;
            crate::leanh::lean_dec(v_val_3355_);
            v___x_3357_ = (crate::leanh::lean_unbox(v_defValue_3351_) as u8);
            return v___x_3357_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_opts_3358_: *mut crate::leanh::LeanObject,
    mut v_opt_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3360_: u8 = 0;
    let mut v_r_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3360_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_3358_, v_opt_3359_);
    crate::leanh::lean_dec_ref(v_opt_3359_);
    crate::leanh::lean_dec_ref(v_opts_3358_);
    v_r_3361_ = crate::leanh::lean_box((v_res_3360_) as usize);
    return v_r_3361_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3362_ = crate::leanh::lean_box(1);
    v___x_3363_ = l_Lean_MessageData_ofFormat(v___x_3362_);
    return v___x_3363_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3367_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2;
    v___x_3368_ = l_Lean_MessageData_ofFormat(v___x_3367_);
    return v___x_3368_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(
    mut v_x_3369_: *mut crate::leanh::LeanObject,
    mut v_x_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3375_: u8 = 0;
    let mut v_before_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut v_unused_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3370_) == 0 {
                    return v_x_3369_;
                } else {
                    v_head_3371_ = crate::leanh::lean_ctor_get(v_x_3370_, 0);
                    v_tail_3372_ = crate::leanh::lean_ctor_get(v_x_3370_, 1);
                    v_isSharedCheck_3394_ = (!crate::leanh::lean_is_exclusive(v_x_3370_)) as u8;
                    if v_isSharedCheck_3394_ == 0 {
                        v___x_3374_ = v_x_3370_;
                        v_isShared_3375_ = v_isSharedCheck_3394_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3372_);
                        crate::leanh::lean_inc(v_head_3371_);
                        crate::leanh::lean_dec(v_x_3370_);
                        v___x_3374_ = crate::leanh::lean_box(0);
                        v_isShared_3375_ = v_isSharedCheck_3394_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3376_ = crate::leanh::lean_ctor_get(v_head_3371_, 0);
                v_isSharedCheck_3392_ = (!crate::leanh::lean_is_exclusive(v_head_3371_)) as u8;
                if v_isSharedCheck_3392_ == 0 {
                    v_unused_3393_ = crate::leanh::lean_ctor_get(v_head_3371_, 1);
                    crate::leanh::lean_dec(v_unused_3393_);
                    v___x_3378_ = v_head_3371_;
                    v_isShared_3379_ = v_isSharedCheck_3392_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_3376_);
                    crate::leanh::lean_dec(v_head_3371_);
                    v___x_3378_ = crate::leanh::lean_box(0);
                    v_isShared_3379_ = v_isSharedCheck_3392_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3380_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_3379_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3378_, 7);
                    crate::leanh::lean_ctor_set(v___x_3378_, 1, v___x_3380_);
                    crate::leanh::lean_ctor_set(v___x_3378_, 0, v_x_3369_);
                    v___x_3382_ = v___x_3378_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_x_3369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 1, v___x_3380_);
                    v___x_3382_ = v_reuseFailAlloc_3391_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3383_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
                if v_isShared_3375_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3374_, 7);
                    crate::leanh::lean_ctor_set(v___x_3374_, 1, v___x_3383_);
                    crate::leanh::lean_ctor_set(v___x_3374_, 0, v___x_3382_);
                    v___x_3385_ = v___x_3374_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3383_);
                    v___x_3385_ = v_reuseFailAlloc_3390_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3386_ = l_Lean_MessageData_ofSyntax(v_before_3376_);
                v___x_3387_ = l_Lean_indentD(v___x_3386_);
                v___x_3388_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3388_, 0, v___x_3385_);
                crate::leanh::lean_ctor_set(v___x_3388_, 1, v___x_3387_);
                v_x_3369_ = v___x_3388_;
                v_x_3370_ = v_tail_3372_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1;
    v___x_3399_ = l_Lean_MessageData_ofFormat(v___x_3398_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(
    mut v_msgData_3400_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: u8 = 0;
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut v_unused_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3404_ = crate::leanh::lean_ctor_get(v___y_3402_, 2);
                v___x_3405_ = l_Lean_Elab_pp_macroStack;
                v___x_3406_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_3404_, v___x_3405_);
                if v___x_3406_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_3401_);
                    v___x_3407_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3407_, 0, v_msgData_3400_);
                    return v___x_3407_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_3401_) == 0 {
                        v___x_3408_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3408_, 0, v_msgData_3400_);
                        return v___x_3408_;
                    } else {
                        v_head_3409_ = crate::leanh::lean_ctor_get(v_macroStack_3401_, 0);
                        crate::leanh::lean_inc(v_head_3409_);
                        v_after_3410_ = crate::leanh::lean_ctor_get(v_head_3409_, 1);
                        v_isSharedCheck_3425_ =
                            (!crate::leanh::lean_is_exclusive(v_head_3409_)) as u8;
                        if v_isSharedCheck_3425_ == 0 {
                            v_unused_3426_ = crate::leanh::lean_ctor_get(v_head_3409_, 0);
                            crate::leanh::lean_dec(v_unused_3426_);
                            v___x_3412_ = v_head_3409_;
                            v_isShared_3413_ = v_isSharedCheck_3425_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_3410_);
                            crate::leanh::lean_dec(v_head_3409_);
                            v___x_3412_ = crate::leanh::lean_box(0);
                            v_isShared_3413_ = v_isSharedCheck_3425_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3414_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_3413_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3412_, 7);
                    crate::leanh::lean_ctor_set(v___x_3412_, 1, v___x_3414_);
                    crate::leanh::lean_ctor_set(v___x_3412_, 0, v_msgData_3400_);
                    v___x_3416_ = v___x_3412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3424_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_msgData_3400_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3414_);
                    v___x_3416_ = v_reuseFailAlloc_3424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3417_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
                v___x_3418_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3418_, 0, v___x_3416_);
                crate::leanh::lean_ctor_set(v___x_3418_, 1, v___x_3417_);
                v___x_3419_ = l_Lean_MessageData_ofSyntax(v_after_3410_);
                v___x_3420_ = l_Lean_indentD(v___x_3419_);
                v_msgData_3421_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_3421_, 0, v___x_3418_);
                crate::leanh::lean_ctor_set(v_msgData_3421_, 1, v___x_3420_);
                v___x_3422_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_3421_, v_macroStack_3401_);
                v___x_3423_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3423_, 0, v___x_3422_);
                return v___x_3423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_msgData_3427_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3431_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3427_, v_macroStack_3428_, v___y_3429_);
    crate::leanh::lean_dec_ref(v___y_3429_);
    return v_res_3431_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(
    mut v_msg_3432_: *mut crate::leanh::LeanObject,
    mut v___y_3433_: *mut crate::leanh::LeanObject,
    mut v___y_3434_: *mut crate::leanh::LeanObject,
    mut v___y_3435_: *mut crate::leanh::LeanObject,
    mut v___y_3436_: *mut crate::leanh::LeanObject,
    mut v___y_3437_: *mut crate::leanh::LeanObject,
    mut v___y_3438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3440_ = crate::leanh::lean_ctor_get(v___y_3437_, 5);
                v___x_3441_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msg_3432_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
                v_a_3442_ = crate::leanh::lean_ctor_get(v___x_3441_, 0);
                crate::leanh::lean_inc(v_a_3442_);
                crate::leanh::lean_dec_ref(v___x_3441_);
                v_macroStack_3443_ = crate::leanh::lean_ctor_get(v___y_3433_, 1);
                v___x_3444_ = l_Lean_Elab_getBetterRef(v_ref_3440_, v_macroStack_3443_);
                crate::leanh::lean_inc(v_macroStack_3443_);
                v___x_3445_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_3442_, v_macroStack_3443_, v___y_3437_);
                v_a_3446_ = crate::leanh::lean_ctor_get(v___x_3445_, 0);
                v_isSharedCheck_3454_ = (!crate::leanh::lean_is_exclusive(v___x_3445_)) as u8;
                if v_isSharedCheck_3454_ == 0 {
                    v___x_3448_ = v___x_3445_;
                    v_isShared_3449_ = v_isSharedCheck_3454_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3446_);
                    crate::leanh::lean_dec(v___x_3445_);
                    v___x_3448_ = crate::leanh::lean_box(0);
                    v_isShared_3449_ = v_isSharedCheck_3454_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3450_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3450_, 0, v___x_3444_);
                crate::leanh::lean_ctor_set(v___x_3450_, 1, v_a_3446_);
                if v_isShared_3449_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3448_, 1);
                    crate::leanh::lean_ctor_set(v___x_3448_, 0, v___x_3450_);
                    v___x_3452_ = v___x_3448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
                    v___x_3452_ = v_reuseFailAlloc_3453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg___boxed(
    mut v_msg_3455_: *mut crate::leanh::LeanObject,
    mut v___y_3456_: *mut crate::leanh::LeanObject,
    mut v___y_3457_: *mut crate::leanh::LeanObject,
    mut v___y_3458_: *mut crate::leanh::LeanObject,
    mut v___y_3459_: *mut crate::leanh::LeanObject,
    mut v___y_3460_: *mut crate::leanh::LeanObject,
    mut v___y_3461_: *mut crate::leanh::LeanObject,
    mut v___y_3462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
    crate::leanh::lean_dec(v___y_3461_);
    crate::leanh::lean_dec_ref(v___y_3460_);
    crate::leanh::lean_dec(v___y_3459_);
    crate::leanh::lean_dec_ref(v___y_3458_);
    crate::leanh::lean_dec(v___y_3457_);
    crate::leanh::lean_dec_ref(v___y_3456_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(
    mut v_e_3464_: *mut crate::leanh::LeanObject,
    mut v___y_3465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3487_: u8 = 0;
    let mut v_unused_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3467_ = l_Lean_Expr_hasMVar(v_e_3464_);
                if v___x_3467_ == 0 {
                    v___x_3468_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3468_, 0, v_e_3464_);
                    return v___x_3468_;
                } else {
                    v___x_3469_ = lean_st_ref_get(v___y_3465_);
                    v_mctx_3470_ = crate::leanh::lean_ctor_get(v___x_3469_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_3470_);
                    crate::leanh::lean_dec(v___x_3469_);
                    v___x_3471_ = l_Lean_instantiateMVarsCore(v_mctx_3470_, v_e_3464_);
                    v_fst_3472_ = crate::leanh::lean_ctor_get(v___x_3471_, 0);
                    crate::leanh::lean_inc(v_fst_3472_);
                    v_snd_3473_ = crate::leanh::lean_ctor_get(v___x_3471_, 1);
                    crate::leanh::lean_inc(v_snd_3473_);
                    crate::leanh::lean_dec_ref(v___x_3471_);
                    v___x_3474_ = lean_st_ref_take(v___y_3465_);
                    v_cache_3475_ = crate::leanh::lean_ctor_get(v___x_3474_, 1);
                    v_zetaDeltaFVarIds_3476_ = crate::leanh::lean_ctor_get(v___x_3474_, 2);
                    v_postponed_3477_ = crate::leanh::lean_ctor_get(v___x_3474_, 3);
                    v_diag_3478_ = crate::leanh::lean_ctor_get(v___x_3474_, 4);
                    v_isSharedCheck_3487_ = (!crate::leanh::lean_is_exclusive(v___x_3474_)) as u8;
                    if v_isSharedCheck_3487_ == 0 {
                        v_unused_3488_ = crate::leanh::lean_ctor_get(v___x_3474_, 0);
                        crate::leanh::lean_dec(v_unused_3488_);
                        v___x_3480_ = v___x_3474_;
                        v_isShared_3481_ = v_isSharedCheck_3487_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_3478_);
                        crate::leanh::lean_inc(v_postponed_3477_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_3476_);
                        crate::leanh::lean_inc(v_cache_3475_);
                        crate::leanh::lean_dec(v___x_3474_);
                        v___x_3480_ = crate::leanh::lean_box(0);
                        v_isShared_3481_ = v_isSharedCheck_3487_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3480_, 0, v_snd_3473_);
                    v___x_3483_ = v___x_3480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3486_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_snd_3473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_cache_3475_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3486_,
                        2,
                        v_zetaDeltaFVarIds_3476_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_postponed_3477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_diag_3478_);
                    v___x_3483_ = v_reuseFailAlloc_3486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3484_ = lean_st_ref_set(v___y_3465_, v___x_3483_);
                v___x_3485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3485_, 0, v_fst_3472_);
                return v___x_3485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(
    mut v_e_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3492_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3489_, v___y_3490_);
    crate::leanh::lean_dec(v___y_3490_);
    return v_res_3492_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3493_ = crate::leanh::lean_box(0);
    v___x_3494_ = l_Lean_Elab_abortTermExceptionId;
    v___x_3495_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3495_, 0, v___x_3494_);
    crate::leanh::lean_ctor_set(v___x_3495_, 1, v___x_3493_);
    return v___x_3495_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3497_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
    v___x_3498_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3498_, 0, v___x_3497_);
    return v___x_3498_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(
    mut v___y_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3500_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v_res_3500_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3502_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0;
    v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
    return v___x_3503_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3504_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1);
    v___x_3505_ = l_Lean_MessageData_ofExpr(v___x_3504_);
    return v___x_3505_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3506_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2);
    v___x_3507_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1);
    v___x_3508_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3507_);
    crate::leanh::lean_ctor_set(v___x_3508_, 1, v___x_3506_);
    return v___x_3508_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3510_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4;
    v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
    return v___x_3511_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3512_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5);
    v___x_3513_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3);
    v___x_3514_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3514_, 0, v___x_3513_);
    crate::leanh::lean_ctor_set(v___x_3514_, 1, v___x_3512_);
    return v___x_3514_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3516_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7;
    v___x_3517_ = l_Lean_stringToMessageData(v___x_3516_);
    return v___x_3517_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3519_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9;
    v___x_3520_ = l_Lean_stringToMessageData(v___x_3519_);
    return v___x_3520_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0(
    mut v_stx_3521_: *mut crate::leanh::LeanObject,
    mut v_a_3522_: *mut crate::leanh::LeanObject,
    mut v_a_3523_: *mut crate::leanh::LeanObject,
    mut v_a_3524_: *mut crate::leanh::LeanObject,
    mut v_a_3525_: *mut crate::leanh::LeanObject,
    mut v_a_3526_: *mut crate::leanh::LeanObject,
    mut v_a_3527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ty_x3f_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3547_: u8 = 0;
    let mut v_cancelTk_x3f_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3549_: u8 = 0;
    let mut v_inheritedTraceOptions_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: u8 = 0;
    let mut v_ref_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: u8 = 0;
    let mut v_id_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3573_: u8 = 0;
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3582_: u8 = 0;
    let mut v_unused_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: u8 = 0;
    let mut v___y_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3612_: u8 = 0;
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3616_: u8 = 0;
    let mut v_a_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut v_a_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3628_: u8 = 0;
    let mut v___x_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3632_: u8 = 0;
    let mut v___y_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: u8 = 0;
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_a_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_3529_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2);
                v___x_3530_ = 1;
                v___x_3531_ = crate::leanh::lean_box(0);
                v___x_3532_ = crate::leanh::lean_box((v___x_3530_) as usize);
                v___x_3533_ = crate::leanh::lean_box((v___x_3530_) as usize);
                crate::leanh::lean_inc(v_stx_3521_);
                v___x_3534_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                crate::leanh::lean_closure_set(v___x_3534_, 0, v_stx_3521_);
                crate::leanh::lean_closure_set(v___x_3534_, 1, v_ty_x3f_3529_);
                crate::leanh::lean_closure_set(v___x_3534_, 2, v___x_3532_);
                crate::leanh::lean_closure_set(v___x_3534_, 3, v___x_3533_);
                crate::leanh::lean_closure_set(v___x_3534_, 4, v___x_3531_);
                v_fileName_3535_ = crate::leanh::lean_ctor_get(v_a_3526_, 0);
                v_fileMap_3536_ = crate::leanh::lean_ctor_get(v_a_3526_, 1);
                v_options_3537_ = crate::leanh::lean_ctor_get(v_a_3526_, 2);
                v_currRecDepth_3538_ = crate::leanh::lean_ctor_get(v_a_3526_, 3);
                v_maxRecDepth_3539_ = crate::leanh::lean_ctor_get(v_a_3526_, 4);
                v_ref_3540_ = crate::leanh::lean_ctor_get(v_a_3526_, 5);
                v_currNamespace_3541_ = crate::leanh::lean_ctor_get(v_a_3526_, 6);
                v_openDecls_3542_ = crate::leanh::lean_ctor_get(v_a_3526_, 7);
                v_initHeartbeats_3543_ = crate::leanh::lean_ctor_get(v_a_3526_, 8);
                v_maxHeartbeats_3544_ = crate::leanh::lean_ctor_get(v_a_3526_, 9);
                v_quotContext_3545_ = crate::leanh::lean_ctor_get(v_a_3526_, 10);
                v_currMacroScope_3546_ = crate::leanh::lean_ctor_get(v_a_3526_, 11);
                v_diag_3547_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3548_ = crate::leanh::lean_ctor_get(v_a_3526_, 12);
                v_suppressElabErrors_3549_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3550_ = crate::leanh::lean_ctor_get(v_a_3526_, 13);
                v___x_3551_ = 1;
                v_ref_3552_ = l_Lean_replaceRef(v_stx_3521_, v_ref_3540_);
                crate::leanh::lean_dec(v_stx_3521_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3550_);
                crate::leanh::lean_inc(v_cancelTk_x3f_3548_);
                crate::leanh::lean_inc(v_currMacroScope_3546_);
                crate::leanh::lean_inc(v_quotContext_3545_);
                crate::leanh::lean_inc(v_maxHeartbeats_3544_);
                crate::leanh::lean_inc(v_initHeartbeats_3543_);
                crate::leanh::lean_inc(v_openDecls_3542_);
                crate::leanh::lean_inc(v_currNamespace_3541_);
                crate::leanh::lean_inc(v_maxRecDepth_3539_);
                crate::leanh::lean_inc(v_currRecDepth_3538_);
                crate::leanh::lean_inc_ref(v_options_3537_);
                crate::leanh::lean_inc_ref(v_fileMap_3536_);
                crate::leanh::lean_inc_ref(v_fileName_3535_);
                v___x_3553_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_3553_, 0, v_fileName_3535_);
                crate::leanh::lean_ctor_set(v___x_3553_, 1, v_fileMap_3536_);
                crate::leanh::lean_ctor_set(v___x_3553_, 2, v_options_3537_);
                crate::leanh::lean_ctor_set(v___x_3553_, 3, v_currRecDepth_3538_);
                crate::leanh::lean_ctor_set(v___x_3553_, 4, v_maxRecDepth_3539_);
                crate::leanh::lean_ctor_set(v___x_3553_, 5, v_ref_3552_);
                crate::leanh::lean_ctor_set(v___x_3553_, 6, v_currNamespace_3541_);
                crate::leanh::lean_ctor_set(v___x_3553_, 7, v_openDecls_3542_);
                crate::leanh::lean_ctor_set(v___x_3553_, 8, v_initHeartbeats_3543_);
                crate::leanh::lean_ctor_set(v___x_3553_, 9, v_maxHeartbeats_3544_);
                crate::leanh::lean_ctor_set(v___x_3553_, 10, v_quotContext_3545_);
                crate::leanh::lean_ctor_set(v___x_3553_, 11, v_currMacroScope_3546_);
                crate::leanh::lean_ctor_set(v___x_3553_, 12, v_cancelTk_x3f_3548_);
                crate::leanh::lean_ctor_set(v___x_3553_, 13, v_inheritedTraceOptions_3550_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3553_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_3547_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3553_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3549_,
                );
                v___x_3554_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        crate::leanh::lean_box(0),
                        v___x_3534_,
                        v___x_3551_,
                        v_a_3522_,
                        v_a_3523_,
                        v_a_3524_,
                        v_a_3525_,
                        v___x_3553_,
                        v_a_3527_,
                    );
                if crate::leanh::lean_obj_tag(v___x_3554_) == 0 {
                    v_a_3555_ = crate::leanh::lean_ctor_get(v___x_3554_, 0);
                    crate::leanh::lean_inc(v_a_3555_);
                    crate::leanh::lean_dec_ref_known(v___x_3554_, 1);
                    v___x_3556_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_3555_, v_a_3525_);
                    v_a_3557_ = crate::leanh::lean_ctor_get(v___x_3556_, 0);
                    crate::leanh::lean_inc(v_a_3557_);
                    crate::leanh::lean_dec_ref(v___x_3556_);
                    v___x_3652_ = l_Lean_Expr_hasSorry(v_a_3557_);
                    if v___x_3652_ == 0 {
                        v___y_3597_ = v_a_3522_;
                        v___y_3598_ = v_a_3523_;
                        v___y_3599_ = v_a_3524_;
                        v___y_3600_ = v_a_3525_;
                        v___y_3601_ = v___x_3553_;
                        v___y_3602_ = v_a_3527_;
                        state = 5;
                        continue;
                    } else {
                        v___x_3653_ = l_Lean_Expr_hasSyntheticSorry(v_a_3557_);
                        if v___x_3653_ == 0 {
                            v___y_3634_ = v_a_3522_;
                            v___y_3635_ = v_a_3523_;
                            v___y_3636_ = v_a_3524_;
                            v___y_3637_ = v_a_3525_;
                            v___y_3638_ = v___x_3553_;
                            v___y_3639_ = v_a_3527_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3557_);
                            crate::leanh::lean_dec_ref_known(v___x_3553_, 14);
                            v___x_3654_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_3655_ = crate::leanh::lean_ctor_get(v___x_3654_, 0);
                            v_isSharedCheck_3662_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3654_)) as u8;
                            if v_isSharedCheck_3662_ == 0 {
                                v___x_3657_ = v___x_3654_;
                                v_isShared_3658_ = v_isSharedCheck_3662_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3655_);
                                crate::leanh::lean_dec(v___x_3654_);
                                v___x_3657_ = crate::leanh::lean_box(0);
                                v_isShared_3658_ = v_isSharedCheck_3662_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3553_, 14);
                    v_a_3663_ = crate::leanh::lean_ctor_get(v___x_3554_, 0);
                    v_isSharedCheck_3670_ = (!crate::leanh::lean_is_exclusive(v___x_3554_)) as u8;
                    if v_isSharedCheck_3670_ == 0 {
                        v___x_3665_ = v___x_3554_;
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3663_);
                        crate::leanh::lean_dec(v___x_3554_);
                        v___x_3665_ = crate::leanh::lean_box(0);
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3568_ == 0 {
                    if crate::leanh::lean_obj_tag(v___y_3560_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___y_3560_, 2);
                        crate::leanh::lean_dec_ref(v___y_3561_);
                        crate::leanh::lean_dec(v_a_3557_);
                        return v___y_3564_;
                    } else {
                        v_id_3569_ = crate::leanh::lean_ctor_get(v___y_3560_, 0);
                        v_isSharedCheck_3582_ =
                            (!crate::leanh::lean_is_exclusive(v___y_3560_)) as u8;
                        if v_isSharedCheck_3582_ == 0 {
                            v_unused_3583_ = crate::leanh::lean_ctor_get(v___y_3560_, 1);
                            crate::leanh::lean_dec(v_unused_3583_);
                            v___x_3571_ = v___y_3560_;
                            v_isShared_3572_ = v_isSharedCheck_3582_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_id_3569_);
                            crate::leanh::lean_dec(v___y_3560_);
                            v___x_3571_ = crate::leanh::lean_box(0);
                            v_isShared_3572_ = v_isSharedCheck_3582_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3561_);
                    crate::leanh::lean_dec_ref(v___y_3560_);
                    crate::leanh::lean_dec(v_a_3557_);
                    return v___y_3564_;
                }
            }
            2 => {
                v___x_3573_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3565_, v_id_3569_);
                crate::leanh::lean_dec(v_id_3569_);
                if v___x_3573_ == 0 {
                    crate::leanh::lean_del_object(v___x_3571_);
                    crate::leanh::lean_dec_ref(v___y_3561_);
                    crate::leanh::lean_dec(v_a_3557_);
                    return v___y_3564_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3564_);
                    v___x_3574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6);
                    v___x_3575_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8);
                    v___x_3576_ = l_Lean_indentExpr(v_a_3557_);
                    if v_isShared_3572_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3571_, 7);
                        crate::leanh::lean_ctor_set(v___x_3571_, 1, v___x_3576_);
                        crate::leanh::lean_ctor_set(v___x_3571_, 0, v___x_3575_);
                        v___x_3578_ = v___x_3571_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3581_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3575_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3581_, 1, v___x_3576_);
                        v___x_3578_ = v_reuseFailAlloc_3581_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3579_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                crate::leanh::lean_ctor_set(v___x_3579_, 1, v___x_3574_);
                v___x_3580_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3579_, v___y_3559_, v___y_3567_, v___y_3563_, v___y_3566_, v___y_3561_, v___y_3562_);
                crate::leanh::lean_dec_ref(v___y_3561_);
                return v___x_3580_;
            }
            4 => {
                crate::leanh::lean_inc(v_a_3557_);
                v___x_3591_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr(v_a_3557_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
                if crate::leanh::lean_obj_tag(v___x_3591_) == 0 {
                    crate::leanh::lean_dec_ref(v___y_3589_);
                    crate::leanh::lean_dec(v_a_3557_);
                    return v___x_3591_;
                } else {
                    v_a_3592_ = crate::leanh::lean_ctor_get(v___x_3591_, 0);
                    crate::leanh::lean_inc(v_a_3592_);
                    v___x_3593_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_3594_ = l_Lean_Exception_isInterrupt(v_a_3592_);
                    if v___x_3594_ == 0 {
                        crate::leanh::lean_inc(v_a_3592_);
                        v___x_3595_ = l_Lean_Exception_isRuntime(v_a_3592_);
                        v___y_3559_ = v___y_3585_;
                        v___y_3560_ = v_a_3592_;
                        v___y_3561_ = v___y_3589_;
                        v___y_3562_ = v___y_3590_;
                        v___y_3563_ = v___y_3587_;
                        v___y_3564_ = v___x_3591_;
                        v___y_3565_ = v___x_3593_;
                        v___y_3566_ = v___y_3588_;
                        v___y_3567_ = v___y_3586_;
                        v___y_3568_ = v___x_3595_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3559_ = v___y_3585_;
                        v___y_3560_ = v_a_3592_;
                        v___y_3561_ = v___y_3589_;
                        v___y_3562_ = v___y_3590_;
                        v___y_3563_ = v___y_3587_;
                        v___y_3564_ = v___x_3591_;
                        v___y_3565_ = v___x_3593_;
                        v___y_3566_ = v___y_3588_;
                        v___y_3567_ = v___y_3586_;
                        v___y_3568_ = v___x_3594_;
                        state = 1;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_3557_);
                v___x_3603_ = l_Lean_Meta_getMVars(
                    v_a_3557_,
                    v___y_3599_,
                    v___y_3600_,
                    v___y_3601_,
                    v___y_3602_,
                );
                if crate::leanh::lean_obj_tag(v___x_3603_) == 0 {
                    v_a_3604_ = crate::leanh::lean_ctor_get(v___x_3603_, 0);
                    crate::leanh::lean_inc(v_a_3604_);
                    crate::leanh::lean_dec_ref_known(v___x_3603_, 1);
                    v___x_3605_ = l_Lean_Elab_Term_logUnassignedUsingErrorInfos(
                        v_a_3604_,
                        v___x_3531_,
                        v___y_3597_,
                        v___y_3598_,
                        v___y_3599_,
                        v___y_3600_,
                        v___y_3601_,
                        v___y_3602_,
                    );
                    crate::leanh::lean_dec(v_a_3604_);
                    if crate::leanh::lean_obj_tag(v___x_3605_) == 0 {
                        v_a_3606_ = crate::leanh::lean_ctor_get(v___x_3605_, 0);
                        crate::leanh::lean_inc(v_a_3606_);
                        crate::leanh::lean_dec_ref_known(v___x_3605_, 1);
                        v___x_3607_ = (crate::leanh::lean_unbox(v_a_3606_) as u8);
                        crate::leanh::lean_dec(v_a_3606_);
                        if v___x_3607_ == 0 {
                            v___y_3585_ = v___y_3597_;
                            v___y_3586_ = v___y_3598_;
                            v___y_3587_ = v___y_3599_;
                            v___y_3588_ = v___y_3600_;
                            v___y_3589_ = v___y_3601_;
                            v___y_3590_ = v___y_3602_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_3601_);
                            crate::leanh::lean_dec(v_a_3557_);
                            v___x_3608_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_3609_ = crate::leanh::lean_ctor_get(v___x_3608_, 0);
                            v_isSharedCheck_3616_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3608_)) as u8;
                            if v_isSharedCheck_3616_ == 0 {
                                v___x_3611_ = v___x_3608_;
                                v_isShared_3612_ = v_isSharedCheck_3616_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3609_);
                                crate::leanh::lean_dec(v___x_3608_);
                                v___x_3611_ = crate::leanh::lean_box(0);
                                v_isShared_3612_ = v_isSharedCheck_3616_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3601_);
                        crate::leanh::lean_dec(v_a_3557_);
                        v_a_3617_ = crate::leanh::lean_ctor_get(v___x_3605_, 0);
                        v_isSharedCheck_3624_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3605_)) as u8;
                        if v_isSharedCheck_3624_ == 0 {
                            v___x_3619_ = v___x_3605_;
                            v_isShared_3620_ = v_isSharedCheck_3624_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3617_);
                            crate::leanh::lean_dec(v___x_3605_);
                            v___x_3619_ = crate::leanh::lean_box(0);
                            v_isShared_3620_ = v_isSharedCheck_3624_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3601_);
                    crate::leanh::lean_dec(v_a_3557_);
                    v_a_3625_ = crate::leanh::lean_ctor_get(v___x_3603_, 0);
                    v_isSharedCheck_3632_ = (!crate::leanh::lean_is_exclusive(v___x_3603_)) as u8;
                    if v_isSharedCheck_3632_ == 0 {
                        v___x_3627_ = v___x_3603_;
                        v_isShared_3628_ = v_isSharedCheck_3632_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3625_);
                        crate::leanh::lean_dec(v___x_3603_);
                        v___x_3627_ = crate::leanh::lean_box(0);
                        v_isShared_3628_ = v_isSharedCheck_3632_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3612_ == 0 {
                    v___x_3614_ = v___x_3611_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3615_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
                    v___x_3614_ = v_reuseFailAlloc_3615_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3614_;
            }
            8 => {
                if v_isShared_3620_ == 0 {
                    v___x_3622_ = v___x_3619_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3623_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
                    v___x_3622_ = v_reuseFailAlloc_3623_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3622_;
            }
            10 => {
                if v_isShared_3628_ == 0 {
                    v___x_3630_ = v___x_3627_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
                    v___x_3630_ = v_reuseFailAlloc_3631_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3630_;
            }
            12 => {
                v___x_3640_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10);
                v___x_3641_ = l_Lean_indentExpr(v_a_3557_);
                v___x_3642_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3642_, 0, v___x_3640_);
                crate::leanh::lean_ctor_set(v___x_3642_, 1, v___x_3641_);
                v___x_3643_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3642_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
                crate::leanh::lean_dec_ref(v___y_3638_);
                v_a_3644_ = crate::leanh::lean_ctor_get(v___x_3643_, 0);
                v_isSharedCheck_3651_ = (!crate::leanh::lean_is_exclusive(v___x_3643_)) as u8;
                if v_isSharedCheck_3651_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    v_isShared_3647_ = v_isSharedCheck_3651_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3644_);
                    crate::leanh::lean_dec(v___x_3643_);
                    v___x_3646_ = crate::leanh::lean_box(0);
                    v_isShared_3647_ = v_isSharedCheck_3651_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_3647_ == 0 {
                    v___x_3649_ = v___x_3646_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
                    v___x_3649_ = v_reuseFailAlloc_3650_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3649_;
            }
            15 => {
                if v_isShared_3658_ == 0 {
                    v___x_3660_ = v___x_3657_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3661_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
                    v___x_3660_ = v_reuseFailAlloc_3661_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3660_;
            }
            17 => {
                if v_isShared_3666_ == 0 {
                    v___x_3668_ = v___x_3665_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
                    v___x_3668_ = v_reuseFailAlloc_3669_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3668_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___boxed(
    mut v_stx_3671_: *mut crate::leanh::LeanObject,
    mut v_a_3672_: *mut crate::leanh::LeanObject,
    mut v_a_3673_: *mut crate::leanh::LeanObject,
    mut v_a_3674_: *mut crate::leanh::LeanObject,
    mut v_a_3675_: *mut crate::leanh::LeanObject,
    mut v_a_3676_: *mut crate::leanh::LeanObject,
    mut v_a_3677_: *mut crate::leanh::LeanObject,
    mut v_a_3678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0(v_stx_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
    crate::leanh::lean_dec(v_a_3677_);
    crate::leanh::lean_dec_ref(v_a_3676_);
    crate::leanh::lean_dec(v_a_3675_);
    crate::leanh::lean_dec_ref(v_a_3674_);
    crate::leanh::lean_dec(v_a_3673_);
    crate::leanh::lean_dec_ref(v_a_3672_);
    return v_res_3679_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0(
    mut v_config_3711_: *mut crate::leanh::LeanObject,
    mut v_item_3712_: *mut crate::leanh::LeanObject,
    mut v___y_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_item_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v_grind_3753_: u8 = 0;
    let mut v_star_3754_: u8 = 0;
    let mut v_all_3755_: u8 = 0;
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3758_: u8 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: u8 = 0;
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_isSharedCheck_3767_: u8 = 0;
    let mut v_a_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut v_a_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v_grind_3792_: u8 = 0;
    let mut v_try_x3f_3793_: u8 = 0;
    let mut v_all_3794_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_isSharedCheck_3806_: u8 = 0;
    let mut v_a_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_a_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_try_x3f_3831_: u8 = 0;
    let mut v_star_3832_: u8 = 0;
    let mut v_all_3833_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v_isSharedCheck_3845_: u8 = 0;
    let mut v_a_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v_a_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v___x_3862_: u8 = 0;
    let mut v_value_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v_grind_3873_: u8 = 0;
    let mut v_try_x3f_3874_: u8 = 0;
    let mut v_star_3875_: u8 = 0;
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3886_: u8 = 0;
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_a_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_a_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_a_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3730_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5;
                v___x_3731_ = l_Lean_Elab_ConfigEval_ConfigItem_addCompletionInfo(
                    v_item_3712_,
                    v___x_3730_,
                    v___y_3713_,
                    v___y_3714_,
                    v___y_3715_,
                    v___y_3716_,
                    v___y_3717_,
                    v___y_3718_,
                );
                if crate::leanh::lean_obj_tag(v___x_3731_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3731_, 1);
                    v___x_3732_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3712_);
                    if v___x_3732_ == 0 {
                        v___x_3733_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3712_);
                        crate::leanh::lean_inc_ref(v_item_3712_);
                        v___x_3734_ = l_Lean_Elab_ConfigEval_ConfigItem_shift(v_item_3712_);
                        v___x_3735_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1;
                        v___x_3736_ = lean_string_dec_eq(v___x_3733_, v___x_3735_);
                        if v___x_3736_ == 0 {
                            v___x_3737_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__2;
                            v___x_3738_ = lean_string_dec_eq(v___x_3733_, v___x_3737_);
                            if v___x_3738_ == 0 {
                                v___x_3739_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3;
                                v___x_3740_ = lean_string_dec_eq(v___x_3733_, v___x_3739_);
                                if v___x_3740_ == 0 {
                                    v___x_3741_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4;
                                    v___x_3742_ = lean_string_dec_eq(v___x_3733_, v___x_3741_);
                                    if v___x_3742_ == 0 {
                                        v___x_3743_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5;
                                        v___x_3744_ = lean_string_dec_eq(v___x_3733_, v___x_3743_);
                                        crate::leanh::lean_dec_ref(v___x_3733_);
                                        if v___x_3744_ == 0 {
                                            crate::leanh::lean_dec_ref(v_item_3712_);
                                            crate::leanh::lean_dec_ref(v_config_3711_);
                                            v_item_3721_ = v___x_3734_;
                                            v___y_3722_ = v___y_3713_;
                                            v___y_3723_ = v___y_3714_;
                                            v___y_3724_ = v___y_3715_;
                                            v___y_3725_ = v___y_3716_;
                                            v___y_3726_ = v___y_3717_;
                                            v___y_3727_ = v___y_3718_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_3745_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6;
                                            v___x_3746_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                    v_item_3712_,
                                                    v___x_3745_,
                                                    v___y_3713_,
                                                    v___y_3714_,
                                                    v___y_3715_,
                                                    v___y_3716_,
                                                    v___y_3717_,
                                                    v___y_3718_,
                                                );
                                            if crate::leanh::lean_obj_tag(v___x_3746_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_3746_, 1);
                                                v___x_3747_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_3734_,
                                                    );
                                                if v___x_3747_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_item_3712_);
                                                    crate::leanh::lean_dec_ref(v_config_3711_);
                                                    v_item_3721_ = v___x_3734_;
                                                    v___y_3722_ = v___y_3713_;
                                                    v___y_3723_ = v___y_3714_;
                                                    v___y_3724_ = v___y_3715_;
                                                    v___y_3725_ = v___y_3716_;
                                                    v___y_3726_ = v___y_3717_;
                                                    v___y_3727_ = v___y_3718_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3734_);
                                                    v___x_3748_ =
                                                        l_Lean_Elab_ConfigEval_evalBoolItem(
                                                            v_item_3712_,
                                                            v___y_3713_,
                                                            v___y_3714_,
                                                            v___y_3715_,
                                                            v___y_3716_,
                                                            v___y_3717_,
                                                            v___y_3718_,
                                                        );
                                                    if crate::leanh::lean_obj_tag(v___x_3748_) == 0
                                                    {
                                                        v_a_3749_ = crate::leanh::lean_ctor_get(
                                                            v___x_3748_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3767_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_3748_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3767_ == 0 {
                                                            v___x_3751_ = v___x_3748_;
                                                            v_isShared_3752_ =
                                                                v_isSharedCheck_3767_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_3749_);
                                                            crate::leanh::lean_dec(v___x_3748_);
                                                            v___x_3751_ = crate::leanh::lean_box(0);
                                                            v_isShared_3752_ =
                                                                v_isSharedCheck_3767_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_config_3711_);
                                                        v_a_3768_ = crate::leanh::lean_ctor_get(
                                                            v___x_3748_,
                                                            0,
                                                        );
                                                        v_isSharedCheck_3775_ =
                                                            (!crate::leanh::lean_is_exclusive(
                                                                v___x_3748_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_3775_ == 0 {
                                                            v___x_3770_ = v___x_3748_;
                                                            v_isShared_3771_ =
                                                                v_isSharedCheck_3775_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            crate::leanh::lean_inc(v_a_3768_);
                                                            crate::leanh::lean_dec(v___x_3748_);
                                                            v___x_3770_ = crate::leanh::lean_box(0);
                                                            v_isShared_3771_ =
                                                                v_isSharedCheck_3775_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3734_);
                                                crate::leanh::lean_dec_ref(v_item_3712_);
                                                crate::leanh::lean_dec_ref(v_config_3711_);
                                                v_a_3776_ =
                                                    crate::leanh::lean_ctor_get(v___x_3746_, 0);
                                                v_isSharedCheck_3783_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3746_))
                                                        as u8;
                                                if v_isSharedCheck_3783_ == 0 {
                                                    v___x_3778_ = v___x_3746_;
                                                    v_isShared_3779_ = v_isSharedCheck_3783_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3776_);
                                                    crate::leanh::lean_dec(v___x_3746_);
                                                    v___x_3778_ = crate::leanh::lean_box(0);
                                                    v_isShared_3779_ = v_isSharedCheck_3783_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_3733_);
                                        v___x_3784_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7;
                                        v___x_3785_ =
                                            l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                                v_item_3712_,
                                                v___x_3784_,
                                                v___y_3713_,
                                                v___y_3714_,
                                                v___y_3715_,
                                                v___y_3716_,
                                                v___y_3717_,
                                                v___y_3718_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_3785_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_3785_, 1);
                                            v___x_3786_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_3734_,
                                                );
                                            if v___x_3786_ == 0 {
                                                crate::leanh::lean_dec_ref(v_item_3712_);
                                                crate::leanh::lean_dec_ref(v_config_3711_);
                                                v_item_3721_ = v___x_3734_;
                                                v___y_3722_ = v___y_3713_;
                                                v___y_3723_ = v___y_3714_;
                                                v___y_3724_ = v___y_3715_;
                                                v___y_3725_ = v___y_3716_;
                                                v___y_3726_ = v___y_3717_;
                                                v___y_3727_ = v___y_3718_;
                                                state = 1;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v___x_3734_);
                                                v___x_3787_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_3712_,
                                                    v___y_3713_,
                                                    v___y_3714_,
                                                    v___y_3715_,
                                                    v___y_3716_,
                                                    v___y_3717_,
                                                    v___y_3718_,
                                                );
                                                if crate::leanh::lean_obj_tag(v___x_3787_) == 0 {
                                                    v_a_3788_ =
                                                        crate::leanh::lean_ctor_get(v___x_3787_, 0);
                                                    v_isSharedCheck_3806_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3787_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3806_ == 0 {
                                                        v___x_3790_ = v___x_3787_;
                                                        v_isShared_3791_ = v_isSharedCheck_3806_;
                                                        state = 10;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_3788_);
                                                        crate::leanh::lean_dec(v___x_3787_);
                                                        v___x_3790_ = crate::leanh::lean_box(0);
                                                        v_isShared_3791_ = v_isSharedCheck_3806_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v_config_3711_);
                                                    v_a_3807_ =
                                                        crate::leanh::lean_ctor_get(v___x_3787_, 0);
                                                    v_isSharedCheck_3814_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_3787_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_3814_ == 0 {
                                                        v___x_3809_ = v___x_3787_;
                                                        v_isShared_3810_ = v_isSharedCheck_3814_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_3807_);
                                                        crate::leanh::lean_dec(v___x_3787_);
                                                        v___x_3809_ = crate::leanh::lean_box(0);
                                                        v_isShared_3810_ = v_isSharedCheck_3814_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3734_);
                                            crate::leanh::lean_dec_ref(v_item_3712_);
                                            crate::leanh::lean_dec_ref(v_config_3711_);
                                            v_a_3815_ = crate::leanh::lean_ctor_get(v___x_3785_, 0);
                                            v_isSharedCheck_3822_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_3785_))
                                                    as u8;
                                            if v_isSharedCheck_3822_ == 0 {
                                                v___x_3817_ = v___x_3785_;
                                                v_isShared_3818_ = v_isSharedCheck_3822_;
                                                state = 16;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_3815_);
                                                crate::leanh::lean_dec(v___x_3785_);
                                                v___x_3817_ = crate::leanh::lean_box(0);
                                                v_isShared_3818_ = v_isSharedCheck_3822_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3733_);
                                    v___x_3823_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8;
                                    v___x_3824_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                        v_item_3712_,
                                        v___x_3823_,
                                        v___y_3713_,
                                        v___y_3714_,
                                        v___y_3715_,
                                        v___y_3716_,
                                        v___y_3717_,
                                        v___y_3718_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3824_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3824_, 1);
                                        v___x_3825_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_3734_,
                                        );
                                        if v___x_3825_ == 0 {
                                            crate::leanh::lean_dec_ref(v_item_3712_);
                                            crate::leanh::lean_dec_ref(v_config_3711_);
                                            v_item_3721_ = v___x_3734_;
                                            v___y_3722_ = v___y_3713_;
                                            v___y_3723_ = v___y_3714_;
                                            v___y_3724_ = v___y_3715_;
                                            v___y_3725_ = v___y_3716_;
                                            v___y_3726_ = v___y_3717_;
                                            v___y_3727_ = v___y_3718_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec_ref(v___x_3734_);
                                            v___x_3826_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_3712_,
                                                v___y_3713_,
                                                v___y_3714_,
                                                v___y_3715_,
                                                v___y_3716_,
                                                v___y_3717_,
                                                v___y_3718_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_3826_) == 0 {
                                                v_a_3827_ =
                                                    crate::leanh::lean_ctor_get(v___x_3826_, 0);
                                                v_isSharedCheck_3845_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3826_))
                                                        as u8;
                                                if v_isSharedCheck_3845_ == 0 {
                                                    v___x_3829_ = v___x_3826_;
                                                    v_isShared_3830_ = v_isSharedCheck_3845_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3827_);
                                                    crate::leanh::lean_dec(v___x_3826_);
                                                    v___x_3829_ = crate::leanh::lean_box(0);
                                                    v_isShared_3830_ = v_isSharedCheck_3845_;
                                                    state = 18;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec_ref(v_config_3711_);
                                                v_a_3846_ =
                                                    crate::leanh::lean_ctor_get(v___x_3826_, 0);
                                                v_isSharedCheck_3853_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_3826_))
                                                        as u8;
                                                if v_isSharedCheck_3853_ == 0 {
                                                    v___x_3848_ = v___x_3826_;
                                                    v_isShared_3849_ = v_isSharedCheck_3853_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_3846_);
                                                    crate::leanh::lean_dec(v___x_3826_);
                                                    v___x_3848_ = crate::leanh::lean_box(0);
                                                    v_isShared_3849_ = v_isSharedCheck_3853_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_3734_);
                                        crate::leanh::lean_dec_ref(v_item_3712_);
                                        crate::leanh::lean_dec_ref(v_config_3711_);
                                        v_a_3854_ = crate::leanh::lean_ctor_get(v___x_3824_, 0);
                                        v_isSharedCheck_3861_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3824_)) as u8;
                                        if v_isSharedCheck_3861_ == 0 {
                                            v___x_3856_ = v___x_3824_;
                                            v_isShared_3857_ = v_isSharedCheck_3861_;
                                            state = 24;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3854_);
                                            crate::leanh::lean_dec(v___x_3824_);
                                            v___x_3856_ = crate::leanh::lean_box(0);
                                            v_isShared_3857_ = v_isSharedCheck_3861_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3733_);
                                crate::leanh::lean_dec_ref(v_config_3711_);
                                v___x_3862_ =
                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3734_);
                                if v___x_3862_ == 0 {
                                    crate::leanh::lean_dec_ref(v_item_3712_);
                                    v_item_3721_ = v___x_3734_;
                                    v___y_3722_ = v___y_3713_;
                                    v___y_3723_ = v___y_3714_;
                                    v___y_3724_ = v___y_3715_;
                                    v___y_3725_ = v___y_3716_;
                                    v___y_3726_ = v___y_3717_;
                                    v___y_3727_ = v___y_3718_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3734_);
                                    v_value_3863_ = crate::leanh::lean_ctor_get(v_item_3712_, 2);
                                    crate::leanh::lean_inc(v_value_3863_);
                                    crate::leanh::lean_dec_ref(v_item_3712_);
                                    v___x_3864_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0(v_value_3863_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
                                    return v___x_3864_;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3733_);
                            v___x_3865_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9;
                            v___x_3866_ = l_Lean_Elab_ConfigEval_ConfigItem_addConstInfo(
                                v_item_3712_,
                                v___x_3865_,
                                v___y_3713_,
                                v___y_3714_,
                                v___y_3715_,
                                v___y_3716_,
                                v___y_3717_,
                                v___y_3718_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_3866_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3866_, 1);
                                v___x_3867_ =
                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3734_);
                                if v___x_3867_ == 0 {
                                    crate::leanh::lean_dec_ref(v_item_3712_);
                                    crate::leanh::lean_dec_ref(v_config_3711_);
                                    v_item_3721_ = v___x_3734_;
                                    v___y_3722_ = v___y_3713_;
                                    v___y_3723_ = v___y_3714_;
                                    v___y_3724_ = v___y_3715_;
                                    v___y_3725_ = v___y_3716_;
                                    v___y_3726_ = v___y_3717_;
                                    v___y_3727_ = v___y_3718_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3734_);
                                    v___x_3868_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                        v_item_3712_,
                                        v___y_3713_,
                                        v___y_3714_,
                                        v___y_3715_,
                                        v___y_3716_,
                                        v___y_3717_,
                                        v___y_3718_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3868_) == 0 {
                                        v_a_3869_ = crate::leanh::lean_ctor_get(v___x_3868_, 0);
                                        v_isSharedCheck_3887_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3868_)) as u8;
                                        if v_isSharedCheck_3887_ == 0 {
                                            v___x_3871_ = v___x_3868_;
                                            v_isShared_3872_ = v_isSharedCheck_3887_;
                                            state = 26;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3869_);
                                            crate::leanh::lean_dec(v___x_3868_);
                                            v___x_3871_ = crate::leanh::lean_box(0);
                                            v_isShared_3872_ = v_isSharedCheck_3887_;
                                            state = 26;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_config_3711_);
                                        v_a_3888_ = crate::leanh::lean_ctor_get(v___x_3868_, 0);
                                        v_isSharedCheck_3895_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3868_)) as u8;
                                        if v_isSharedCheck_3895_ == 0 {
                                            v___x_3890_ = v___x_3868_;
                                            v_isShared_3891_ = v_isSharedCheck_3895_;
                                            state = 30;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3888_);
                                            crate::leanh::lean_dec(v___x_3868_);
                                            v___x_3890_ = crate::leanh::lean_box(0);
                                            v_isShared_3891_ = v_isSharedCheck_3895_;
                                            state = 30;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_3734_);
                                crate::leanh::lean_dec_ref(v_item_3712_);
                                crate::leanh::lean_dec_ref(v_config_3711_);
                                v_a_3896_ = crate::leanh::lean_ctor_get(v___x_3866_, 0);
                                v_isSharedCheck_3903_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3866_)) as u8;
                                if v_isSharedCheck_3903_ == 0 {
                                    v___x_3898_ = v___x_3866_;
                                    v_isShared_3899_ = v_isSharedCheck_3903_;
                                    state = 32;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3896_);
                                    crate::leanh::lean_dec(v___x_3866_);
                                    v___x_3898_ = crate::leanh::lean_box(0);
                                    v_isShared_3899_ = v_isSharedCheck_3903_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_config_3711_);
                        v_item_3721_ = v_item_3712_;
                        v___y_3722_ = v___y_3713_;
                        v___y_3723_ = v___y_3714_;
                        v___y_3724_ = v___y_3715_;
                        v___y_3725_ = v___y_3716_;
                        v___y_3726_ = v___y_3717_;
                        v___y_3727_ = v___y_3718_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_item_3712_);
                    crate::leanh::lean_dec_ref(v_config_3711_);
                    v_a_3904_ = crate::leanh::lean_ctor_get(v___x_3731_, 0);
                    v_isSharedCheck_3911_ = (!crate::leanh::lean_is_exclusive(v___x_3731_)) as u8;
                    if v_isSharedCheck_3911_ == 0 {
                        v___x_3906_ = v___x_3731_;
                        v_isShared_3907_ = v_isSharedCheck_3911_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3904_);
                        crate::leanh::lean_dec(v___x_3731_);
                        v___x_3906_ = crate::leanh::lean_box(0);
                        v_isShared_3907_ = v_isSharedCheck_3911_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3728_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__0;
                v___x_3729_ = l_Lean_Elab_ConfigEval_ConfigItem_throwInvalidOption___redArg(
                    v_item_3721_,
                    v___x_3728_,
                    v___y_3722_,
                    v___y_3723_,
                    v___y_3724_,
                    v___y_3725_,
                    v___y_3726_,
                    v___y_3727_,
                );
                return v___x_3729_;
            }
            2 => {
                v_grind_3753_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 0 as u32);
                v_star_3754_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 2 as u32);
                v_all_3755_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 3 as u32);
                v_isSharedCheck_3766_ = (!crate::leanh::lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3766_ == 0 {
                    v___x_3757_ = v_config_3711_;
                    v_isShared_3758_ = v_isSharedCheck_3766_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_config_3711_);
                    v___x_3757_ = crate::leanh::lean_box(0);
                    v_isShared_3758_ = v_isSharedCheck_3766_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3758_ == 0 {
                    v___x_3760_ = v___x_3757_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3765_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3765_,
                        0 as u32,
                        v_grind_3753_,
                    );
                    v___x_3760_ = v_reuseFailAlloc_3765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3761_ = (crate::leanh::lean_unbox(v_a_3749_) as u8);
                crate::leanh::lean_dec(v_a_3749_);
                crate::leanh::lean_ctor_set_uint8(v___x_3760_, 1 as u32, v___x_3761_);
                crate::leanh::lean_ctor_set_uint8(v___x_3760_, 2 as u32, v_star_3754_);
                crate::leanh::lean_ctor_set_uint8(v___x_3760_, 3 as u32, v_all_3755_);
                if v_isShared_3752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3751_, 0, v___x_3760_);
                    v___x_3763_ = v___x_3751_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3760_);
                    v___x_3763_ = v_reuseFailAlloc_3764_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3763_;
            }
            6 => {
                if v_isShared_3771_ == 0 {
                    v___x_3773_ = v___x_3770_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
                    v___x_3773_ = v_reuseFailAlloc_3774_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3773_;
            }
            8 => {
                if v_isShared_3779_ == 0 {
                    v___x_3781_ = v___x_3778_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
                    v___x_3781_ = v_reuseFailAlloc_3782_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3781_;
            }
            10 => {
                v_grind_3792_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 0 as u32);
                v_try_x3f_3793_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 1 as u32);
                v_all_3794_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 3 as u32);
                v_isSharedCheck_3805_ = (!crate::leanh::lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3805_ == 0 {
                    v___x_3796_ = v_config_3711_;
                    v_isShared_3797_ = v_isSharedCheck_3805_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_config_3711_);
                    v___x_3796_ = crate::leanh::lean_box(0);
                    v_isShared_3797_ = v_isSharedCheck_3805_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3797_ == 0 {
                    v___x_3799_ = v___x_3796_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3804_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3804_,
                        0 as u32,
                        v_grind_3792_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3804_,
                        1 as u32,
                        v_try_x3f_3793_,
                    );
                    v___x_3799_ = v_reuseFailAlloc_3804_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3800_ = (crate::leanh::lean_unbox(v_a_3788_) as u8);
                crate::leanh::lean_dec(v_a_3788_);
                crate::leanh::lean_ctor_set_uint8(v___x_3799_, 2 as u32, v___x_3800_);
                crate::leanh::lean_ctor_set_uint8(v___x_3799_, 3 as u32, v_all_3794_);
                if v_isShared_3791_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3790_, 0, v___x_3799_);
                    v___x_3802_ = v___x_3790_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3799_);
                    v___x_3802_ = v_reuseFailAlloc_3803_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3802_;
            }
            14 => {
                if v_isShared_3810_ == 0 {
                    v___x_3812_ = v___x_3809_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3813_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
                    v___x_3812_ = v_reuseFailAlloc_3813_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3812_;
            }
            16 => {
                if v_isShared_3818_ == 0 {
                    v___x_3820_ = v___x_3817_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
                    v___x_3820_ = v_reuseFailAlloc_3821_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3820_;
            }
            18 => {
                v_try_x3f_3831_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 1 as u32);
                v_star_3832_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 2 as u32);
                v_all_3833_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 3 as u32);
                v_isSharedCheck_3844_ = (!crate::leanh::lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3844_ == 0 {
                    v___x_3835_ = v_config_3711_;
                    v_isShared_3836_ = v_isSharedCheck_3844_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_config_3711_);
                    v___x_3835_ = crate::leanh::lean_box(0);
                    v_isShared_3836_ = v_isSharedCheck_3844_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3836_ == 0 {
                    v___x_3838_ = v___x_3835_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    v___x_3838_ = v_reuseFailAlloc_3843_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3839_ = (crate::leanh::lean_unbox(v_a_3827_) as u8);
                crate::leanh::lean_dec(v_a_3827_);
                crate::leanh::lean_ctor_set_uint8(v___x_3838_, 0 as u32, v___x_3839_);
                crate::leanh::lean_ctor_set_uint8(v___x_3838_, 1 as u32, v_try_x3f_3831_);
                crate::leanh::lean_ctor_set_uint8(v___x_3838_, 2 as u32, v_star_3832_);
                crate::leanh::lean_ctor_set_uint8(v___x_3838_, 3 as u32, v_all_3833_);
                if v_isShared_3830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3829_, 0, v___x_3838_);
                    v___x_3841_ = v___x_3829_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3838_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3841_;
            }
            22 => {
                if v_isShared_3849_ == 0 {
                    v___x_3851_ = v___x_3848_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3852_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
                    v___x_3851_ = v_reuseFailAlloc_3852_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3851_;
            }
            24 => {
                if v_isShared_3857_ == 0 {
                    v___x_3859_ = v___x_3856_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3859_;
            }
            26 => {
                v_grind_3873_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 0 as u32);
                v_try_x3f_3874_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 1 as u32);
                v_star_3875_ = crate::leanh::lean_ctor_get_uint8(v_config_3711_, 2 as u32);
                v_isSharedCheck_3886_ = (!crate::leanh::lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3886_ == 0 {
                    v___x_3877_ = v_config_3711_;
                    v_isShared_3878_ = v_isSharedCheck_3886_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_config_3711_);
                    v___x_3877_ = crate::leanh::lean_box(0);
                    v_isShared_3878_ = v_isSharedCheck_3886_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_3878_ == 0 {
                    v___x_3880_ = v___x_3877_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3885_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3885_,
                        0 as u32,
                        v_grind_3873_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3885_,
                        1 as u32,
                        v_try_x3f_3874_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3885_,
                        2 as u32,
                        v_star_3875_,
                    );
                    v___x_3880_ = v_reuseFailAlloc_3885_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_3881_ = (crate::leanh::lean_unbox(v_a_3869_) as u8);
                crate::leanh::lean_dec(v_a_3869_);
                crate::leanh::lean_ctor_set_uint8(v___x_3880_, 3 as u32, v___x_3881_);
                if v_isShared_3872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3871_, 0, v___x_3880_);
                    v___x_3883_ = v___x_3871_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3880_);
                    v___x_3883_ = v_reuseFailAlloc_3884_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3883_;
            }
            30 => {
                if v_isShared_3891_ == 0 {
                    v___x_3893_ = v___x_3890_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
                    v___x_3893_ = v_reuseFailAlloc_3894_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3893_;
            }
            32 => {
                if v_isShared_3899_ == 0 {
                    v___x_3901_ = v___x_3898_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
                    v___x_3901_ = v_reuseFailAlloc_3902_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3901_;
            }
            34 => {
                if v_isShared_3907_ == 0 {
                    v___x_3909_ = v___x_3906_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3910_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
                    v___x_3909_ = v_reuseFailAlloc_3910_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3909_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___boxed(
    mut v_config_3912_: *mut crate::leanh::LeanObject,
    mut v_item_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
    mut v___y_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3921_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0(v_config_3912_, v_item_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
    crate::leanh::lean_dec(v___y_3919_);
    crate::leanh::lean_dec_ref(v___y_3918_);
    crate::leanh::lean_dec(v___y_3917_);
    crate::leanh::lean_dec_ref(v___y_3916_);
    crate::leanh::lean_dec(v___y_3915_);
    crate::leanh::lean_dec_ref(v___y_3914_);
    return v_res_3921_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0(
    mut v_e_3924_: *mut crate::leanh::LeanObject,
    mut v___y_3925_: *mut crate::leanh::LeanObject,
    mut v___y_3926_: *mut crate::leanh::LeanObject,
    mut v___y_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3924_, v___y_3928_);
    return v___x_3932_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___boxed(
    mut v_e_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
    mut v___y_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
    mut v___y_3939_: *mut crate::leanh::LeanObject,
    mut v___y_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3941_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0(v_e_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
    crate::leanh::lean_dec(v___y_3939_);
    crate::leanh::lean_dec_ref(v___y_3938_);
    crate::leanh::lean_dec(v___y_3937_);
    crate::leanh::lean_dec_ref(v___y_3936_);
    crate::leanh::lean_dec(v___y_3935_);
    crate::leanh::lean_dec_ref(v___y_3934_);
    return v_res_3941_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2(
    mut v_00_u03b1_3942_: *mut crate::leanh::LeanObject,
    mut v___y_3943_: *mut crate::leanh::LeanObject,
    mut v___y_3944_: *mut crate::leanh::LeanObject,
    mut v___y_3945_: *mut crate::leanh::LeanObject,
    mut v___y_3946_: *mut crate::leanh::LeanObject,
    mut v___y_3947_: *mut crate::leanh::LeanObject,
    mut v___y_3948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3950_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v___x_3950_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___boxed(
    mut v_00_u03b1_3951_: *mut crate::leanh::LeanObject,
    mut v___y_3952_: *mut crate::leanh::LeanObject,
    mut v___y_3953_: *mut crate::leanh::LeanObject,
    mut v___y_3954_: *mut crate::leanh::LeanObject,
    mut v___y_3955_: *mut crate::leanh::LeanObject,
    mut v___y_3956_: *mut crate::leanh::LeanObject,
    mut v___y_3957_: *mut crate::leanh::LeanObject,
    mut v___y_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
    crate::leanh::lean_dec(v___y_3957_);
    crate::leanh::lean_dec_ref(v___y_3956_);
    crate::leanh::lean_dec(v___y_3955_);
    crate::leanh::lean_dec_ref(v___y_3954_);
    crate::leanh::lean_dec(v___y_3953_);
    crate::leanh::lean_dec_ref(v___y_3952_);
    return v_res_3959_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1(
    mut v_00_u03b1_3960_: *mut crate::leanh::LeanObject,
    mut v_msg_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3969_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
    return v___x_3969_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___boxed(
    mut v_00_u03b1_3970_: *mut crate::leanh::LeanObject,
    mut v_msg_3971_: *mut crate::leanh::LeanObject,
    mut v___y_3972_: *mut crate::leanh::LeanObject,
    mut v___y_3973_: *mut crate::leanh::LeanObject,
    mut v___y_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_3970_, v_msg_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
    crate::leanh::lean_dec(v___y_3977_);
    crate::leanh::lean_dec_ref(v___y_3976_);
    crate::leanh::lean_dec(v___y_3975_);
    crate::leanh::lean_dec_ref(v___y_3974_);
    crate::leanh::lean_dec(v___y_3973_);
    crate::leanh::lean_dec_ref(v___y_3972_);
    return v_res_3979_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2(
    mut v_msgData_3980_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3989_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3980_, v_macroStack_3981_, v___y_3986_);
    return v___x_3989_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(
    mut v_msgData_3990_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3999_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_3990_, v_macroStack_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
    crate::leanh::lean_dec(v___y_3997_);
    crate::leanh::lean_dec_ref(v___y_3996_);
    crate::leanh::lean_dec(v___y_3995_);
    crate::leanh::lean_dec_ref(v___y_3994_);
    crate::leanh::lean_dec(v___y_3993_);
    crate::leanh::lean_dec_ref(v___y_3992_);
    return v_res_3999_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4000_ = crate::leanh::lean_box(0);
    v___x_4001_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5;
    v___x_4002_ = l_Lean_mkConst(v___x_4001_, v___x_4000_);
    return v___x_4002_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4003_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0,
    );
    v___x_4004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4004_, 0, v___x_4003_);
    return v___x_4004_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0(
    mut v_cfg_4005_: *mut crate::leanh::LeanObject,
    mut v_cfgItem_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4014_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1,
    );
    v___x_4015_ = l_Lean_Elab_ConfigEval_EvalConfigItem_defaultOnErr___redArg(
        v_cfg_4005_,
        v_cfgItem_4006_,
        v___x_4014_,
        v___y_4007_,
        v___y_4008_,
        v___y_4009_,
        v___y_4010_,
        v___y_4011_,
        v___y_4012_,
    );
    return v___x_4015_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___boxed(
    mut v_cfg_4016_: *mut crate::leanh::LeanObject,
    mut v_cfgItem_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4025_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0(
        v_cfg_4016_,
        v_cfgItem_4017_,
        v___y_4018_,
        v___y_4019_,
        v___y_4020_,
        v___y_4021_,
        v___y_4022_,
        v___y_4023_,
    );
    crate::leanh::lean_dec(v___y_4023_);
    crate::leanh::lean_dec_ref(v___y_4022_);
    crate::leanh::lean_dec(v___y_4021_);
    crate::leanh::lean_dec_ref(v___y_4020_);
    crate::leanh::lean_dec(v___y_4019_);
    crate::leanh::lean_dec_ref(v___y_4018_);
    crate::leanh::lean_dec(v_cfgItem_4017_);
    return v_res_4025_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
    mut v_cfg_4027_: *mut crate::leanh::LeanObject,
    mut v_init_4028_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_4029_: u8,
    mut v_a_4030_: *mut crate::leanh::LeanObject,
    mut v_a_4031_: *mut crate::leanh::LeanObject,
    mut v_a_4032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_onErr_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eval_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_onErr_4034_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0;
    v_eval_4035_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0;
    if v_logExceptions_4029_ == 0 {
        let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4036_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_4035_,
            v_init_4028_,
            v_cfg_4027_,
            v_onErr_4034_,
            v_logExceptions_4029_,
            v_a_4031_,
            v_a_4032_,
        );
        return v___x_4036_;
    } else {
        let mut v_recover_4037_: u8 = 0;
        let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_recover_4037_ = crate::leanh::lean_ctor_get_uint8(
            v_a_4030_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        );
        v___x_4038_ = l_Lean_Elab_ConfigEval_EvalConfigItem_setConfig_x27___redArg(
            v_eval_4035_,
            v_init_4028_,
            v_cfg_4027_,
            v_onErr_4034_,
            v_recover_4037_,
            v_a_4031_,
            v_a_4032_,
        );
        return v___x_4038_;
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___boxed(
    mut v_cfg_4039_: *mut crate::leanh::LeanObject,
    mut v_init_4040_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_4041_: *mut crate::leanh::LeanObject,
    mut v_a_4042_: *mut crate::leanh::LeanObject,
    mut v_a_4043_: *mut crate::leanh::LeanObject,
    mut v_a_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_4046_: u8 = 0;
    let mut v_res_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_4046_ = (crate::leanh::lean_unbox(v_logExceptions_4041_) as u8);
    v_res_4047_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
        v_cfg_4039_,
        v_init_4040_,
        v_logExceptions_boxed_4046_,
        v_a_4042_,
        v_a_4043_,
        v_a_4044_,
    );
    crate::leanh::lean_dec(v_a_4044_);
    crate::leanh::lean_dec_ref(v_a_4043_);
    crate::leanh::lean_dec_ref(v_a_4042_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig(
    mut v_cfg_4048_: *mut crate::leanh::LeanObject,
    mut v_init_4049_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_4050_: u8,
    mut v_a_4051_: *mut crate::leanh::LeanObject,
    mut v_a_4052_: *mut crate::leanh::LeanObject,
    mut v_a_4053_: *mut crate::leanh::LeanObject,
    mut v_a_4054_: *mut crate::leanh::LeanObject,
    mut v_a_4055_: *mut crate::leanh::LeanObject,
    mut v_a_4056_: *mut crate::leanh::LeanObject,
    mut v_a_4057_: *mut crate::leanh::LeanObject,
    mut v_a_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4060_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
        v_cfg_4048_,
        v_init_4049_,
        v_logExceptions_4050_,
        v_a_4051_,
        v_a_4057_,
        v_a_4058_,
    );
    return v___x_4060_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___boxed(
    mut v_cfg_4061_: *mut crate::leanh::LeanObject,
    mut v_init_4062_: *mut crate::leanh::LeanObject,
    mut v_logExceptions_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
    mut v_a_4065_: *mut crate::leanh::LeanObject,
    mut v_a_4066_: *mut crate::leanh::LeanObject,
    mut v_a_4067_: *mut crate::leanh::LeanObject,
    mut v_a_4068_: *mut crate::leanh::LeanObject,
    mut v_a_4069_: *mut crate::leanh::LeanObject,
    mut v_a_4070_: *mut crate::leanh::LeanObject,
    mut v_a_4071_: *mut crate::leanh::LeanObject,
    mut v_a_4072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_logExceptions_boxed_4073_: u8 = 0;
    let mut v_res_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_4073_ = (crate::leanh::lean_unbox(v_logExceptions_4063_) as u8);
    v_res_4074_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig(
        v_cfg_4061_,
        v_init_4062_,
        v_logExceptions_boxed_4073_,
        v_a_4064_,
        v_a_4065_,
        v_a_4066_,
        v_a_4067_,
        v_a_4068_,
        v_a_4069_,
        v_a_4070_,
        v_a_4071_,
    );
    crate::leanh::lean_dec(v_a_4071_);
    crate::leanh::lean_dec_ref(v_a_4070_);
    crate::leanh::lean_dec(v_a_4069_);
    crate::leanh::lean_dec_ref(v_a_4068_);
    crate::leanh::lean_dec(v_a_4067_);
    crate::leanh::lean_dec_ref(v_a_4066_);
    crate::leanh::lean_dec(v_a_4065_);
    crate::leanh::lean_dec_ref(v_a_4064_);
    return v_res_4074_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(
    mut v_e_4075_: *mut crate::leanh::LeanObject,
    mut v___y_4076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_unused_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4078_ = l_Lean_Expr_hasMVar(v_e_4075_);
                if v___x_4078_ == 0 {
                    v___x_4079_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4079_, 0, v_e_4075_);
                    return v___x_4079_;
                } else {
                    v___x_4080_ = lean_st_ref_get(v___y_4076_);
                    v_mctx_4081_ = crate::leanh::lean_ctor_get(v___x_4080_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4081_);
                    crate::leanh::lean_dec(v___x_4080_);
                    v___x_4082_ = l_Lean_instantiateMVarsCore(v_mctx_4081_, v_e_4075_);
                    v_fst_4083_ = crate::leanh::lean_ctor_get(v___x_4082_, 0);
                    crate::leanh::lean_inc(v_fst_4083_);
                    v_snd_4084_ = crate::leanh::lean_ctor_get(v___x_4082_, 1);
                    crate::leanh::lean_inc(v_snd_4084_);
                    crate::leanh::lean_dec_ref(v___x_4082_);
                    v___x_4085_ = lean_st_ref_take(v___y_4076_);
                    v_cache_4086_ = crate::leanh::lean_ctor_get(v___x_4085_, 1);
                    v_zetaDeltaFVarIds_4087_ = crate::leanh::lean_ctor_get(v___x_4085_, 2);
                    v_postponed_4088_ = crate::leanh::lean_ctor_get(v___x_4085_, 3);
                    v_diag_4089_ = crate::leanh::lean_ctor_get(v___x_4085_, 4);
                    v_isSharedCheck_4098_ = (!crate::leanh::lean_is_exclusive(v___x_4085_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v_unused_4099_ = crate::leanh::lean_ctor_get(v___x_4085_, 0);
                        crate::leanh::lean_dec(v_unused_4099_);
                        v___x_4091_ = v___x_4085_;
                        v_isShared_4092_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4089_);
                        crate::leanh::lean_inc(v_postponed_4088_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4087_);
                        crate::leanh::lean_inc(v_cache_4086_);
                        crate::leanh::lean_dec(v___x_4085_);
                        v___x_4091_ = crate::leanh::lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4092_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4091_, 0, v_snd_4084_);
                    v___x_4094_ = v___x_4091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_snd_4084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 1, v_cache_4086_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4097_,
                        2,
                        v_zetaDeltaFVarIds_4087_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 3, v_postponed_4088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4097_, 4, v_diag_4089_);
                    v___x_4094_ = v_reuseFailAlloc_4097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4095_ = lean_st_ref_set(v___y_4076_, v___x_4094_);
                v___x_4096_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4096_, 0, v_fst_4083_);
                return v___x_4096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg___boxed(
    mut v_e_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4103_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(
            v_e_4100_,
            v___y_4101_,
        );
    crate::leanh::lean_dec(v___y_4101_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0(
    mut v_e_4104_: *mut crate::leanh::LeanObject,
    mut v___y_4105_: *mut crate::leanh::LeanObject,
    mut v___y_4106_: *mut crate::leanh::LeanObject,
    mut v___y_4107_: *mut crate::leanh::LeanObject,
    mut v___y_4108_: *mut crate::leanh::LeanObject,
    mut v___y_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4114_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(
            v_e_4104_,
            v___y_4110_,
        );
    return v___x_4114_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___boxed(
    mut v_e_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4125_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0(
        v_e_4115_,
        v___y_4116_,
        v___y_4117_,
        v___y_4118_,
        v___y_4119_,
        v___y_4120_,
        v___y_4121_,
        v___y_4122_,
        v___y_4123_,
    );
    crate::leanh::lean_dec(v___y_4123_);
    crate::leanh::lean_dec_ref(v___y_4122_);
    crate::leanh::lean_dec(v___y_4121_);
    crate::leanh::lean_dec_ref(v___y_4120_);
    crate::leanh::lean_dec(v___y_4119_);
    crate::leanh::lean_dec_ref(v___y_4118_);
    crate::leanh::lean_dec(v___y_4117_);
    crate::leanh::lean_dec_ref(v___y_4116_);
    return v_res_4125_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0(
    mut v_x_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4130_);
    crate::leanh::lean_inc_ref(v___y_4129_);
    crate::leanh::lean_inc(v___y_4128_);
    crate::leanh::lean_inc_ref(v___y_4127_);
    v___x_4136_ = crate::leanh::lean_apply_9(
        v_x_4126_,
        v___y_4127_,
        v___y_4128_,
        v___y_4129_,
        v___y_4130_,
        v___y_4131_,
        v___y_4132_,
        v___y_4133_,
        v___y_4134_,
        crate::leanh::lean_box(0),
    );
    return v___x_4136_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0___boxed(
    mut v_x_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
    mut v___y_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4147_ =
        l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0(
            v_x_4137_,
            v___y_4138_,
            v___y_4139_,
            v___y_4140_,
            v___y_4141_,
            v___y_4142_,
            v___y_4143_,
            v___y_4144_,
            v___y_4145_,
        );
    crate::leanh::lean_dec(v___y_4141_);
    crate::leanh::lean_dec_ref(v___y_4140_);
    crate::leanh::lean_dec(v___y_4139_);
    crate::leanh::lean_dec_ref(v___y_4138_);
    return v_res_4147_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(
    mut v_mctx_4148_: *mut crate::leanh::LeanObject,
    mut v_x_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
    mut v___y_4154_: *mut crate::leanh::LeanObject,
    mut v___y_4155_: *mut crate::leanh::LeanObject,
    mut v___y_4156_: *mut crate::leanh::LeanObject,
    mut v___y_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4153_);
                crate::leanh::lean_inc_ref(v___y_4152_);
                crate::leanh::lean_inc(v___y_4151_);
                crate::leanh::lean_inc_ref(v___y_4150_);
                v___f_4159_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_4159_, 0, v_x_4149_);
                crate::leanh::lean_closure_set(v___f_4159_, 1, v___y_4150_);
                crate::leanh::lean_closure_set(v___f_4159_, 2, v___y_4151_);
                crate::leanh::lean_closure_set(v___f_4159_, 3, v___y_4152_);
                crate::leanh::lean_closure_set(v___f_4159_, 4, v___y_4153_);
                v___x_4160_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(
                    crate::leanh::lean_box(0),
                    v_mctx_4148_,
                    v___f_4159_,
                    v___y_4154_,
                    v___y_4155_,
                    v___y_4156_,
                    v___y_4157_,
                );
                if crate::leanh::lean_obj_tag(v___x_4160_) == 0 {
                    return v___x_4160_;
                } else {
                    v_a_4161_ = crate::leanh::lean_ctor_get(v___x_4160_, 0);
                    v_isSharedCheck_4168_ = (!crate::leanh::lean_is_exclusive(v___x_4160_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4163_ = v___x_4160_;
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4161_);
                        crate::leanh::lean_dec(v___x_4160_);
                        v___x_4163_ = crate::leanh::lean_box(0);
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4164_ == 0 {
                    v___x_4166_ = v___x_4163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
                    v___x_4166_ = v_reuseFailAlloc_4167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___boxed(
    mut v_mctx_4169_: *mut crate::leanh::LeanObject,
    mut v_x_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
    mut v___y_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(
        v_mctx_4169_,
        v_x_4170_,
        v___y_4171_,
        v___y_4172_,
        v___y_4173_,
        v___y_4174_,
        v___y_4175_,
        v___y_4176_,
        v___y_4177_,
        v___y_4178_,
    );
    crate::leanh::lean_dec(v___y_4178_);
    crate::leanh::lean_dec_ref(v___y_4177_);
    crate::leanh::lean_dec(v___y_4176_);
    crate::leanh::lean_dec_ref(v___y_4175_);
    crate::leanh::lean_dec(v___y_4174_);
    crate::leanh::lean_dec_ref(v___y_4173_);
    crate::leanh::lean_dec(v___y_4172_);
    crate::leanh::lean_dec_ref(v___y_4171_);
    return v_res_4180_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1(
    mut v_00_u03b1_4181_: *mut crate::leanh::LeanObject,
    mut v_mctx_4182_: *mut crate::leanh::LeanObject,
    mut v_x_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4193_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(
        v_mctx_4182_,
        v_x_4183_,
        v___y_4184_,
        v___y_4185_,
        v___y_4186_,
        v___y_4187_,
        v___y_4188_,
        v___y_4189_,
        v___y_4190_,
        v___y_4191_,
    );
    return v___x_4193_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___boxed(
    mut v_00_u03b1_4194_: *mut crate::leanh::LeanObject,
    mut v_mctx_4195_: *mut crate::leanh::LeanObject,
    mut v_x_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
    mut v___y_4202_: *mut crate::leanh::LeanObject,
    mut v___y_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1(
        v_00_u03b1_4194_,
        v_mctx_4195_,
        v_x_4196_,
        v___y_4197_,
        v___y_4198_,
        v___y_4199_,
        v___y_4200_,
        v___y_4201_,
        v___y_4202_,
        v___y_4203_,
        v___y_4204_,
    );
    crate::leanh::lean_dec(v___y_4204_);
    crate::leanh::lean_dec_ref(v___y_4203_);
    crate::leanh::lean_dec(v___y_4202_);
    crate::leanh::lean_dec_ref(v___y_4201_);
    crate::leanh::lean_dec(v___y_4200_);
    crate::leanh::lean_dec_ref(v___y_4199_);
    crate::leanh::lean_dec(v___y_4198_);
    crate::leanh::lean_dec_ref(v___y_4197_);
    return v_res_4206_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg(
    mut v_e_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4210_: u8 = 0;
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_unused_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4210_ = l_Lean_Expr_hasMVar(v_e_4207_);
                if v___x_4210_ == 0 {
                    v___x_4211_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4211_, 0, v_e_4207_);
                    return v___x_4211_;
                } else {
                    v___x_4212_ = lean_st_ref_get(v___y_4208_);
                    v_mctx_4213_ = crate::leanh::lean_ctor_get(v___x_4212_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_4213_);
                    crate::leanh::lean_dec(v___x_4212_);
                    v___x_4214_ = l_Lean_instantiateMVarsCore(v_mctx_4213_, v_e_4207_);
                    v_fst_4215_ = crate::leanh::lean_ctor_get(v___x_4214_, 0);
                    crate::leanh::lean_inc(v_fst_4215_);
                    v_snd_4216_ = crate::leanh::lean_ctor_get(v___x_4214_, 1);
                    crate::leanh::lean_inc(v_snd_4216_);
                    crate::leanh::lean_dec_ref(v___x_4214_);
                    v___x_4217_ = lean_st_ref_take(v___y_4208_);
                    v_cache_4218_ = crate::leanh::lean_ctor_get(v___x_4217_, 1);
                    v_zetaDeltaFVarIds_4219_ = crate::leanh::lean_ctor_get(v___x_4217_, 2);
                    v_postponed_4220_ = crate::leanh::lean_ctor_get(v___x_4217_, 3);
                    v_diag_4221_ = crate::leanh::lean_ctor_get(v___x_4217_, 4);
                    v_isSharedCheck_4230_ = (!crate::leanh::lean_is_exclusive(v___x_4217_)) as u8;
                    if v_isSharedCheck_4230_ == 0 {
                        v_unused_4231_ = crate::leanh::lean_ctor_get(v___x_4217_, 0);
                        crate::leanh::lean_dec(v_unused_4231_);
                        v___x_4223_ = v___x_4217_;
                        v_isShared_4224_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_4221_);
                        crate::leanh::lean_inc(v_postponed_4220_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_4219_);
                        crate::leanh::lean_inc(v_cache_4218_);
                        crate::leanh::lean_dec(v___x_4217_);
                        v___x_4223_ = crate::leanh::lean_box(0);
                        v_isShared_4224_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4224_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4223_, 0, v_snd_4216_);
                    v___x_4226_ = v___x_4223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_snd_4216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_cache_4218_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4229_,
                        2,
                        v_zetaDeltaFVarIds_4219_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 3, v_postponed_4220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 4, v_diag_4221_);
                    v___x_4226_ = v_reuseFailAlloc_4229_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4227_ = lean_st_ref_set(v___y_4208_, v___x_4226_);
                v___x_4228_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4228_, 0, v_fst_4215_);
                return v___x_4228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg___boxed(
    mut v_e_4232_: *mut crate::leanh::LeanObject,
    mut v___y_4233_: *mut crate::leanh::LeanObject,
    mut v___y_4234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4235_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg(
            v_e_4232_,
            v___y_4233_,
        );
    crate::leanh::lean_dec(v___y_4233_);
    return v_res_4235_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4(
    mut v_e_4236_: *mut crate::leanh::LeanObject,
    mut v___y_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4242_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg(
            v_e_4236_,
            v___y_4238_,
        );
    return v___x_4242_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___boxed(
    mut v_e_4243_: *mut crate::leanh::LeanObject,
    mut v___y_4244_: *mut crate::leanh::LeanObject,
    mut v___y_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
    mut v___y_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4249_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4(
        v_e_4243_,
        v___y_4244_,
        v___y_4245_,
        v___y_4246_,
        v___y_4247_,
    );
    crate::leanh::lean_dec(v___y_4247_);
    crate::leanh::lean_dec_ref(v___y_4246_);
    crate::leanh::lean_dec(v___y_4245_);
    crate::leanh::lean_dec_ref(v___y_4244_);
    return v_res_4249_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg(
    mut v_mvarId_4250_: *mut crate::leanh::LeanObject,
    mut v_x_4251_: *mut crate::leanh::LeanObject,
    mut v___y_4252_: *mut crate::leanh::LeanObject,
    mut v___y_4253_: *mut crate::leanh::LeanObject,
    mut v___y_4254_: *mut crate::leanh::LeanObject,
    mut v___y_4255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_4250_,
                    v_x_4251_,
                    v___y_4252_,
                    v___y_4253_,
                    v___y_4254_,
                    v___y_4255_,
                );
                if crate::leanh::lean_obj_tag(v___x_4257_) == 0 {
                    v_a_4258_ = crate::leanh::lean_ctor_get(v___x_4257_, 0);
                    v_isSharedCheck_4265_ = (!crate::leanh::lean_is_exclusive(v___x_4257_)) as u8;
                    if v_isSharedCheck_4265_ == 0 {
                        v___x_4260_ = v___x_4257_;
                        v_isShared_4261_ = v_isSharedCheck_4265_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4258_);
                        crate::leanh::lean_dec(v___x_4257_);
                        v___x_4260_ = crate::leanh::lean_box(0);
                        v_isShared_4261_ = v_isSharedCheck_4265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4266_ = crate::leanh::lean_ctor_get(v___x_4257_, 0);
                    v_isSharedCheck_4273_ = (!crate::leanh::lean_is_exclusive(v___x_4257_)) as u8;
                    if v_isSharedCheck_4273_ == 0 {
                        v___x_4268_ = v___x_4257_;
                        v_isShared_4269_ = v_isSharedCheck_4273_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4266_);
                        crate::leanh::lean_dec(v___x_4257_);
                        v___x_4268_ = crate::leanh::lean_box(0);
                        v_isShared_4269_ = v_isSharedCheck_4273_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4261_ == 0 {
                    v___x_4263_ = v___x_4260_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
                    v___x_4263_ = v_reuseFailAlloc_4264_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4263_;
            }
            3 => {
                if v_isShared_4269_ == 0 {
                    v___x_4271_ = v___x_4268_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4272_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
                    v___x_4271_ = v_reuseFailAlloc_4272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4271_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg___boxed(
    mut v_mvarId_4274_: *mut crate::leanh::LeanObject,
    mut v_x_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
    mut v___y_4278_: *mut crate::leanh::LeanObject,
    mut v___y_4279_: *mut crate::leanh::LeanObject,
    mut v___y_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4281_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg(
            v_mvarId_4274_,
            v_x_4275_,
            v___y_4276_,
            v___y_4277_,
            v___y_4278_,
            v___y_4279_,
        );
    crate::leanh::lean_dec(v___y_4279_);
    crate::leanh::lean_dec_ref(v___y_4278_);
    crate::leanh::lean_dec(v___y_4277_);
    crate::leanh::lean_dec_ref(v___y_4276_);
    return v_res_4281_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5(
    mut v_00_u03b1_4282_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4283_: *mut crate::leanh::LeanObject,
    mut v_x_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg(
            v_mvarId_4283_,
            v_x_4284_,
            v___y_4285_,
            v___y_4286_,
            v___y_4287_,
            v___y_4288_,
        );
    return v___x_4290_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___boxed(
    mut v_00_u03b1_4291_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4292_: *mut crate::leanh::LeanObject,
    mut v_x_4293_: *mut crate::leanh::LeanObject,
    mut v___y_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4299_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5(
        v_00_u03b1_4291_,
        v_mvarId_4292_,
        v_x_4293_,
        v___y_4294_,
        v___y_4295_,
        v___y_4296_,
        v___y_4297_,
    );
    crate::leanh::lean_dec(v___y_4297_);
    crate::leanh::lean_dec_ref(v___y_4296_);
    crate::leanh::lean_dec(v___y_4295_);
    crate::leanh::lean_dec_ref(v___y_4294_);
    return v_res_4299_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___redArg(
    mut v_mvarId_4300_: *mut crate::leanh::LeanObject,
    mut v_x_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
    mut v___y_4304_: *mut crate::leanh::LeanObject,
    mut v___y_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
    mut v___y_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_4305_);
                crate::leanh::lean_inc_ref(v___y_4304_);
                crate::leanh::lean_inc(v___y_4303_);
                crate::leanh::lean_inc_ref(v___y_4302_);
                v___f_4311_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_4311_, 0, v_x_4301_);
                crate::leanh::lean_closure_set(v___f_4311_, 1, v___y_4302_);
                crate::leanh::lean_closure_set(v___f_4311_, 2, v___y_4303_);
                crate::leanh::lean_closure_set(v___f_4311_, 3, v___y_4304_);
                crate::leanh::lean_closure_set(v___f_4311_, 4, v___y_4305_);
                v___x_4312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_4300_,
                    v___f_4311_,
                    v___y_4306_,
                    v___y_4307_,
                    v___y_4308_,
                    v___y_4309_,
                );
                if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                    return v___x_4312_;
                } else {
                    v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4320_ = (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4320_ == 0 {
                        v___x_4315_ = v___x_4312_;
                        v_isShared_4316_ = v_isSharedCheck_4320_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4313_);
                        crate::leanh::lean_dec(v___x_4312_);
                        v___x_4315_ = crate::leanh::lean_box(0);
                        v_isShared_4316_ = v_isSharedCheck_4320_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4316_ == 0 {
                    v___x_4318_ = v___x_4315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4319_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
                    v___x_4318_ = v_reuseFailAlloc_4319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___redArg___boxed(
    mut v_mvarId_4321_: *mut crate::leanh::LeanObject,
    mut v_x_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
    mut v___y_4328_: *mut crate::leanh::LeanObject,
    mut v___y_4329_: *mut crate::leanh::LeanObject,
    mut v___y_4330_: *mut crate::leanh::LeanObject,
    mut v___y_4331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4332_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___redArg(
            v_mvarId_4321_,
            v_x_4322_,
            v___y_4323_,
            v___y_4324_,
            v___y_4325_,
            v___y_4326_,
            v___y_4327_,
            v___y_4328_,
            v___y_4329_,
            v___y_4330_,
        );
    crate::leanh::lean_dec(v___y_4330_);
    crate::leanh::lean_dec_ref(v___y_4329_);
    crate::leanh::lean_dec(v___y_4328_);
    crate::leanh::lean_dec_ref(v___y_4327_);
    crate::leanh::lean_dec(v___y_4326_);
    crate::leanh::lean_dec_ref(v___y_4325_);
    crate::leanh::lean_dec(v___y_4324_);
    crate::leanh::lean_dec_ref(v___y_4323_);
    return v_res_4332_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12(
    mut v_00_u03b1_4333_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4334_: *mut crate::leanh::LeanObject,
    mut v_x_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
    mut v___y_4338_: *mut crate::leanh::LeanObject,
    mut v___y_4339_: *mut crate::leanh::LeanObject,
    mut v___y_4340_: *mut crate::leanh::LeanObject,
    mut v___y_4341_: *mut crate::leanh::LeanObject,
    mut v___y_4342_: *mut crate::leanh::LeanObject,
    mut v___y_4343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___redArg(
            v_mvarId_4334_,
            v_x_4335_,
            v___y_4336_,
            v___y_4337_,
            v___y_4338_,
            v___y_4339_,
            v___y_4340_,
            v___y_4341_,
            v___y_4342_,
            v___y_4343_,
        );
    return v___x_4345_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___boxed(
    mut v_00_u03b1_4346_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4347_: *mut crate::leanh::LeanObject,
    mut v_x_4348_: *mut crate::leanh::LeanObject,
    mut v___y_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
    mut v___y_4353_: *mut crate::leanh::LeanObject,
    mut v___y_4354_: *mut crate::leanh::LeanObject,
    mut v___y_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
    mut v___y_4357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4358_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12(
        v_00_u03b1_4346_,
        v_mvarId_4347_,
        v_x_4348_,
        v___y_4349_,
        v___y_4350_,
        v___y_4351_,
        v___y_4352_,
        v___y_4353_,
        v___y_4354_,
        v___y_4355_,
        v___y_4356_,
    );
    crate::leanh::lean_dec(v___y_4356_);
    crate::leanh::lean_dec_ref(v___y_4355_);
    crate::leanh::lean_dec(v___y_4354_);
    crate::leanh::lean_dec_ref(v___y_4353_);
    crate::leanh::lean_dec(v___y_4352_);
    crate::leanh::lean_dec_ref(v___y_4351_);
    crate::leanh::lean_dec(v___y_4350_);
    crate::leanh::lean_dec_ref(v___y_4349_);
    return v_res_4358_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__0(
    mut v___x_4359_: *mut crate::leanh::LeanObject,
    mut v_grind_4360_: u8,
    mut v_try_x3f_4361_: u8,
    mut v_goals_4362_: *mut crate::leanh::LeanObject,
    mut v___y_4363_: *mut crate::leanh::LeanObject,
    mut v___y_4364_: *mut crate::leanh::LeanObject,
    mut v___y_4365_: *mut crate::leanh::LeanObject,
    mut v___y_4366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4368_ = 0;
    v___x_4369_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_4370_ = l_Lean_Meta_LibrarySearch_solveByElim(
        v___x_4359_,
        v___x_4368_,
        v_goals_4362_,
        v___x_4369_,
        v_grind_4360_,
        v_try_x3f_4361_,
        v___y_4363_,
        v___y_4364_,
        v___y_4365_,
        v___y_4366_,
    );
    return v___x_4370_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__0___boxed(
    mut v___x_4371_: *mut crate::leanh::LeanObject,
    mut v_grind_4372_: *mut crate::leanh::LeanObject,
    mut v_try_x3f_4373_: *mut crate::leanh::LeanObject,
    mut v_goals_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
    mut v___y_4376_: *mut crate::leanh::LeanObject,
    mut v___y_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
    mut v___y_4379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_grind_boxed_4380_: u8 = 0;
    let mut v_try_x3f_boxed_4381_: u8 = 0;
    let mut v_res_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_grind_boxed_4380_ = (crate::leanh::lean_unbox(v_grind_4372_) as u8);
    v_try_x3f_boxed_4381_ = (crate::leanh::lean_unbox(v_try_x3f_4373_) as u8);
    v_res_4382_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__0(
        v___x_4371_,
        v_grind_boxed_4380_,
        v_try_x3f_boxed_4381_,
        v_goals_4374_,
        v___y_4375_,
        v___y_4376_,
        v___y_4377_,
        v___y_4378_,
    );
    crate::leanh::lean_dec(v___y_4378_);
    crate::leanh::lean_dec_ref(v___y_4377_);
    crate::leanh::lean_dec(v___y_4376_);
    crate::leanh::lean_dec_ref(v___y_4375_);
    return v_res_4382_;
}
pub unsafe fn l_List_all___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__6(
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_x_4384_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4385_: u8 = 0;
    let mut v_head_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4384_) == 0 {
                    v___x_4385_ = 1;
                    return v___x_4385_;
                } else {
                    v_head_4386_ = crate::leanh::lean_ctor_get(v_x_4384_, 0);
                    crate::leanh::lean_inc(v_head_4386_);
                    v_tail_4387_ = crate::leanh::lean_ctor_get(v_x_4384_, 1);
                    crate::leanh::lean_inc(v_tail_4387_);
                    crate::leanh::lean_dec_ref_known(v_x_4384_, 2);
                    v___x_4388_ = l_Lean_Expr_occurs(v_head_4386_, v_a_4383_);
                    if v___x_4388_ == 0 {
                        crate::leanh::lean_dec(v_tail_4387_);
                        return v___x_4388_;
                    } else {
                        v_x_4384_ = v_tail_4387_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_all___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__6___boxed(
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_x_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4392_: u8 = 0;
    let mut v_r_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4392_ =
        l_List_all___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__6(v_a_4390_, v_x_4391_);
    crate::leanh::lean_dec_ref(v_a_4390_);
    v_r_4393_ = crate::leanh::lean_box((v_res_4392_) as usize);
    return v_r_4393_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__1(
    mut v___x_4394_: *mut crate::leanh::LeanObject,
    mut v_g_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4407_: u8 = 0;
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v_a_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4417_: u8 = 0;
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_g_4395_);
                v___x_4401_ = l_Lean_Expr_mvar___override(v_g_4395_);
                v___x_4402_ = crate::leanh::lean_alloc_closure(l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___boxed as *mut core::ffi::c_void, 6, 1);
                crate::leanh::lean_closure_set(v___x_4402_, 0, v___x_4401_);
                v___x_4403_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg(v_g_4395_, v___x_4402_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
                if crate::leanh::lean_obj_tag(v___x_4403_) == 0 {
                    v_a_4404_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
                    v_isSharedCheck_4413_ = (!crate::leanh::lean_is_exclusive(v___x_4403_)) as u8;
                    if v_isSharedCheck_4413_ == 0 {
                        v___x_4406_ = v___x_4403_;
                        v_isShared_4407_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4404_);
                        crate::leanh::lean_dec(v___x_4403_);
                        v___x_4406_ = crate::leanh::lean_box(0);
                        v_isShared_4407_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4394_);
                    v_a_4414_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
                    v_isSharedCheck_4421_ = (!crate::leanh::lean_is_exclusive(v___x_4403_)) as u8;
                    if v_isSharedCheck_4421_ == 0 {
                        v___x_4416_ = v___x_4403_;
                        v_isShared_4417_ = v_isSharedCheck_4421_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4414_);
                        crate::leanh::lean_dec(v___x_4403_);
                        v___x_4416_ = crate::leanh::lean_box(0);
                        v_isShared_4417_ = v_isSharedCheck_4421_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4408_ = l_List_all___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__6(
                    v_a_4404_,
                    v___x_4394_,
                );
                crate::leanh::lean_dec(v_a_4404_);
                v___x_4409_ = crate::leanh::lean_box((v___x_4408_) as usize);
                if v_isShared_4407_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4406_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
                    v___x_4411_ = v_reuseFailAlloc_4412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4411_;
            }
            3 => {
                if v_isShared_4417_ == 0 {
                    v___x_4419_ = v___x_4416_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4420_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
                    v___x_4419_ = v_reuseFailAlloc_4420_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4419_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__1___boxed(
    mut v___x_4422_: *mut crate::leanh::LeanObject,
    mut v_g_4423_: *mut crate::leanh::LeanObject,
    mut v___y_4424_: *mut crate::leanh::LeanObject,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4429_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__1(
        v___x_4422_,
        v_g_4423_,
        v___y_4424_,
        v___y_4425_,
        v___y_4426_,
        v___y_4427_,
    );
    crate::leanh::lean_dec(v___y_4427_);
    crate::leanh::lean_dec_ref(v___y_4426_);
    crate::leanh::lean_dec(v___y_4425_);
    crate::leanh::lean_dec_ref(v___y_4424_);
    return v_res_4429_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg(
    mut v_msg_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
    mut v___y_4433_: *mut crate::leanh::LeanObject,
    mut v___y_4434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4441_: u8 = 0;
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4436_ = crate::leanh::lean_ctor_get(v___y_4433_, 5);
                v___x_4437_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msg_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
                v_a_4438_ = crate::leanh::lean_ctor_get(v___x_4437_, 0);
                v_isSharedCheck_4446_ = (!crate::leanh::lean_is_exclusive(v___x_4437_)) as u8;
                if v_isSharedCheck_4446_ == 0 {
                    v___x_4440_ = v___x_4437_;
                    v_isShared_4441_ = v_isSharedCheck_4446_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4438_);
                    crate::leanh::lean_dec(v___x_4437_);
                    v___x_4440_ = crate::leanh::lean_box(0);
                    v_isShared_4441_ = v_isSharedCheck_4446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4436_);
                v___x_4442_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4442_, 0, v_ref_4436_);
                crate::leanh::lean_ctor_set(v___x_4442_, 1, v_a_4438_);
                if v_isShared_4441_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4440_, 1);
                    crate::leanh::lean_ctor_set(v___x_4440_, 0, v___x_4442_);
                    v___x_4444_ = v___x_4440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4442_);
                    v___x_4444_ = v_reuseFailAlloc_4445_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4444_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg___boxed(
    mut v_msg_4447_: *mut crate::leanh::LeanObject,
    mut v___y_4448_: *mut crate::leanh::LeanObject,
    mut v___y_4449_: *mut crate::leanh::LeanObject,
    mut v___y_4450_: *mut crate::leanh::LeanObject,
    mut v___y_4451_: *mut crate::leanh::LeanObject,
    mut v___y_4452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4453_ = l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg(
        v_msg_4447_,
        v___y_4448_,
        v___y_4449_,
        v___y_4450_,
        v___y_4451_,
    );
    crate::leanh::lean_dec(v___y_4451_);
    crate::leanh::lean_dec_ref(v___y_4450_);
    crate::leanh::lean_dec(v___y_4449_);
    crate::leanh::lean_dec_ref(v___y_4448_);
    return v_res_4453_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__7(
    mut v_as_4454_: *mut crate::leanh::LeanObject,
    mut v_sz_4455_: usize,
    mut v_i_4456_: usize,
    mut v_b_4457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: usize = 0;
    let mut v___x_4461_: usize = 0;
    let mut v___x_4463_: u8 = 0;
    let mut v_fst_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v_a_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4463_ = lean_usize_dec_lt(v_i_4456_, v_sz_4455_);
                if v___x_4463_ == 0 {
                    return v_b_4457_;
                } else {
                    v_fst_4464_ = crate::leanh::lean_ctor_get(v_b_4457_, 0);
                    v_snd_4465_ = crate::leanh::lean_ctor_get(v_b_4457_, 1);
                    v_isSharedCheck_4480_ = (!crate::leanh::lean_is_exclusive(v_b_4457_)) as u8;
                    if v_isSharedCheck_4480_ == 0 {
                        v___x_4467_ = v_b_4457_;
                        v_isShared_4468_ = v_isSharedCheck_4480_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4465_);
                        crate::leanh::lean_inc(v_fst_4464_);
                        crate::leanh::lean_dec(v_b_4457_);
                        v___x_4467_ = crate::leanh::lean_box(0);
                        v_isShared_4468_ = v_isSharedCheck_4480_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4460_ = 1usize;
                v___x_4461_ = lean_usize_add(v_i_4456_, v___x_4460_);
                v_i_4456_ = v___x_4461_;
                v_b_4457_ = v_a_4459_;
                state = 0;
                continue;
            }
            2 => {
                v_a_4469_ = lean_array_uget_borrowed(v_as_4454_, v_i_4456_);
                v_fst_4470_ = crate::leanh::lean_ctor_get(v_a_4469_, 0);
                v___x_4471_ = l_List_isEmpty___redArg(v_fst_4470_);
                if v___x_4471_ == 0 {
                    crate::leanh::lean_inc(v_a_4469_);
                    v___x_4472_ = lean_array_push(v_snd_4465_, v_a_4469_);
                    if v_isShared_4468_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4467_, 1, v___x_4472_);
                        v___x_4474_ = v___x_4467_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4475_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_fst_4464_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 1, v___x_4472_);
                        v___x_4474_ = v_reuseFailAlloc_4475_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_a_4469_);
                    v___x_4476_ = lean_array_push(v_fst_4464_, v_a_4469_);
                    if v_isShared_4468_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4467_, 0, v___x_4476_);
                        v___x_4478_ = v___x_4467_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4476_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_snd_4465_);
                        v___x_4478_ = v_reuseFailAlloc_4479_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_4459_ = v___x_4474_;
                state = 1;
                continue;
            }
            4 => {
                v_a_4459_ = v___x_4478_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__7___boxed(
    mut v_as_4481_: *mut crate::leanh::LeanObject,
    mut v_sz_4482_: *mut crate::leanh::LeanObject,
    mut v_i_4483_: *mut crate::leanh::LeanObject,
    mut v_b_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4485_: usize = 0;
    let mut v_i_boxed_4486_: usize = 0;
    let mut v_res_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4485_ = crate::leanh::lean_unbox_usize(v_sz_4482_);
    crate::leanh::lean_dec(v_sz_4482_);
    v_i_boxed_4486_ = crate::leanh::lean_unbox_usize(v_i_4483_);
    crate::leanh::lean_dec(v_i_4483_);
    v_res_4487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__7(v_as_4481_, v_sz_boxed_4485_, v_i_boxed_4486_, v_b_4484_);
    crate::leanh::lean_dec_ref(v_as_4481_);
    return v_res_4487_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___lam__0(
    mut v___x_4488_: *mut crate::leanh::LeanObject,
    mut v_a_4489_: *mut crate::leanh::LeanObject,
    mut v_ref_4490_: *mut crate::leanh::LeanObject,
    mut v___x_4491_: u8,
    mut v___y_4492_: *mut crate::leanh::LeanObject,
    mut v___y_4493_: *mut crate::leanh::LeanObject,
    mut v___y_4494_: *mut crate::leanh::LeanObject,
    mut v___y_4495_: *mut crate::leanh::LeanObject,
    mut v___y_4496_: *mut crate::leanh::LeanObject,
    mut v___y_4497_: *mut crate::leanh::LeanObject,
    mut v___y_4498_: *mut crate::leanh::LeanObject,
    mut v___y_4499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4501_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(v___x_4488_, v___y_4497_);
                if crate::leanh::lean_obj_tag(v___x_4501_) == 0 {
                    v_a_4502_ = crate::leanh::lean_ctor_get(v___x_4501_, 0);
                    crate::leanh::lean_inc(v_a_4502_);
                    crate::leanh::lean_dec_ref_known(v___x_4501_, 1);
                    v___x_4503_ = l_Lean_Expr_headBeta(v_a_4502_);
                    v___x_4504_ = crate::leanh::lean_box(0);
                    v___x_4505_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4505_, 0, v_a_4489_);
                    v___x_4506_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(
                        v_ref_4490_,
                        v___x_4503_,
                        v___x_4504_,
                        v___x_4491_,
                        v___x_4504_,
                        v___x_4505_,
                        v___x_4491_,
                        v___y_4492_,
                        v___y_4493_,
                        v___y_4494_,
                        v___y_4495_,
                        v___y_4496_,
                        v___y_4497_,
                        v___y_4498_,
                        v___y_4499_,
                    );
                    return v___x_4506_;
                } else {
                    crate::leanh::lean_dec(v_ref_4490_);
                    crate::leanh::lean_dec_ref(v_a_4489_);
                    v_a_4507_ = crate::leanh::lean_ctor_get(v___x_4501_, 0);
                    v_isSharedCheck_4514_ = (!crate::leanh::lean_is_exclusive(v___x_4501_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4509_ = v___x_4501_;
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4507_);
                        crate::leanh::lean_dec(v___x_4501_);
                        v___x_4509_ = crate::leanh::lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4510_ == 0 {
                    v___x_4512_ = v___x_4509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4512_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___lam__0___boxed(
    mut v___x_4515_: *mut crate::leanh::LeanObject,
    mut v_a_4516_: *mut crate::leanh::LeanObject,
    mut v_ref_4517_: *mut crate::leanh::LeanObject,
    mut v___x_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
    mut v___y_4523_: *mut crate::leanh::LeanObject,
    mut v___y_4524_: *mut crate::leanh::LeanObject,
    mut v___y_4525_: *mut crate::leanh::LeanObject,
    mut v___y_4526_: *mut crate::leanh::LeanObject,
    mut v___y_4527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_20785__boxed_4528_: u8 = 0;
    let mut v_res_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_20785__boxed_4528_ = (crate::leanh::lean_unbox(v___x_4518_) as u8);
    v_res_4529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___lam__0(v___x_4515_, v_a_4516_, v_ref_4517_, v___x_20785__boxed_4528_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
    crate::leanh::lean_dec(v___y_4526_);
    crate::leanh::lean_dec_ref(v___y_4525_);
    crate::leanh::lean_dec(v___y_4524_);
    crate::leanh::lean_dec_ref(v___y_4523_);
    crate::leanh::lean_dec(v___y_4522_);
    crate::leanh::lean_dec_ref(v___y_4521_);
    crate::leanh::lean_dec(v___y_4520_);
    crate::leanh::lean_dec_ref(v___y_4519_);
    return v_res_4529_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8(
    mut v_a_4530_: *mut crate::leanh::LeanObject,
    mut v_a_4531_: *mut crate::leanh::LeanObject,
    mut v_ref_4532_: *mut crate::leanh::LeanObject,
    mut v_as_4533_: *mut crate::leanh::LeanObject,
    mut v_sz_4534_: usize,
    mut v_i_4535_: usize,
    mut v_b_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4546_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: usize = 0;
    let mut v___x_4556_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4546_ = lean_usize_dec_lt(v_i_4535_, v_sz_4534_);
                if v___x_4546_ == 0 {
                    crate::leanh::lean_dec(v_ref_4532_);
                    crate::leanh::lean_dec_ref(v_a_4531_);
                    crate::leanh::lean_dec(v_a_4530_);
                    v___x_4547_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4547_, 0, v_b_4536_);
                    return v___x_4547_;
                } else {
                    v_a_4548_ = lean_array_uget_borrowed(v_as_4533_, v_i_4535_);
                    v_snd_4549_ = crate::leanh::lean_ctor_get(v_a_4548_, 1);
                    crate::leanh::lean_inc(v_a_4530_);
                    v___x_4550_ = l_Lean_mkMVar(v_a_4530_);
                    v___x_4551_ = crate::leanh::lean_box((v___x_4546_) as usize);
                    crate::leanh::lean_inc(v_ref_4532_);
                    crate::leanh::lean_inc_ref(v_a_4531_);
                    v___f_4552_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___lam__0___boxed as *mut core::ffi::c_void, 13, 4);
                    crate::leanh::lean_closure_set(v___f_4552_, 0, v___x_4550_);
                    crate::leanh::lean_closure_set(v___f_4552_, 1, v_a_4531_);
                    crate::leanh::lean_closure_set(v___f_4552_, 2, v_ref_4532_);
                    crate::leanh::lean_closure_set(v___f_4552_, 3, v___x_4551_);
                    crate::leanh::lean_inc(v_snd_4549_);
                    v___x_4553_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(v_snd_4549_, v___f_4552_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
                    if crate::leanh::lean_obj_tag(v___x_4553_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4553_, 1);
                        v___x_4554_ = crate::leanh::lean_box(0);
                        v___x_4555_ = 1usize;
                        v___x_4556_ = lean_usize_add(v_i_4535_, v___x_4555_);
                        v_i_4535_ = v___x_4556_;
                        v_b_4536_ = v___x_4554_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_ref_4532_);
                        crate::leanh::lean_dec_ref(v_a_4531_);
                        crate::leanh::lean_dec(v_a_4530_);
                        return v___x_4553_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___boxed(
    mut v_a_4558_: *mut crate::leanh::LeanObject,
    mut v_a_4559_: *mut crate::leanh::LeanObject,
    mut v_ref_4560_: *mut crate::leanh::LeanObject,
    mut v_as_4561_: *mut crate::leanh::LeanObject,
    mut v_sz_4562_: *mut crate::leanh::LeanObject,
    mut v_i_4563_: *mut crate::leanh::LeanObject,
    mut v_b_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
    mut v___y_4573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4574_: usize = 0;
    let mut v_i_boxed_4575_: usize = 0;
    let mut v_res_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4574_ = crate::leanh::lean_unbox_usize(v_sz_4562_);
    crate::leanh::lean_dec(v_sz_4562_);
    v_i_boxed_4575_ = crate::leanh::lean_unbox_usize(v_i_4563_);
    crate::leanh::lean_dec(v_i_4563_);
    v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8(v_a_4558_, v_a_4559_, v_ref_4560_, v_as_4561_, v_sz_boxed_4574_, v_i_boxed_4575_, v_b_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
    crate::leanh::lean_dec(v___y_4572_);
    crate::leanh::lean_dec_ref(v___y_4571_);
    crate::leanh::lean_dec(v___y_4570_);
    crate::leanh::lean_dec_ref(v___y_4569_);
    crate::leanh::lean_dec(v___y_4568_);
    crate::leanh::lean_dec_ref(v___y_4567_);
    crate::leanh::lean_dec(v___y_4566_);
    crate::leanh::lean_dec_ref(v___y_4565_);
    crate::leanh::lean_dec_ref(v_as_4561_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0(
    mut v___y_4584_: u8,
    mut v_suppressElabErrors_4585_: u8,
    mut v_x_4586_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4586_) == 1 {
        let mut v_pre_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4587_ = crate::leanh::lean_ctor_get(v_x_4586_, 0);
        match crate::leanh::lean_obj_tag(v_pre_4587_) {
            1 => {
                let mut v_pre_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_4588_ = crate::leanh::lean_ctor_get(v_pre_4587_, 0);
                match crate::leanh::lean_obj_tag(v_pre_4588_) {
                    0 => {
                        let mut v_str_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4592_: u8 = 0;
                        v_str_4589_ = crate::leanh::lean_ctor_get(v_x_4586_, 1);
                        v_str_4590_ = crate::leanh::lean_ctor_get(v_pre_4587_, 1);
                        v___x_4591_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0;
                        v___x_4592_ = lean_string_dec_eq(v_str_4590_, v___x_4591_);
                        if v___x_4592_ == 0 {
                            let mut v___x_4593_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4594_: u8 = 0;
                            v___x_4593_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3;
                            v___x_4594_ = lean_string_dec_eq(v_str_4590_, v___x_4593_);
                            if v___x_4594_ == 0 {
                                return v___y_4584_;
                            } else {
                                let mut v___x_4595_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4596_: u8 = 0;
                                v___x_4595_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__1;
                                v___x_4596_ = lean_string_dec_eq(v_str_4589_, v___x_4595_);
                                if v___x_4596_ == 0 {
                                    return v___y_4584_;
                                } else {
                                    return v_suppressElabErrors_4585_;
                                }
                            }
                        } else {
                            let mut v___x_4597_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4598_: u8 = 0;
                            v___x_4597_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__2;
                            v___x_4598_ = lean_string_dec_eq(v_str_4589_, v___x_4597_);
                            if v___x_4598_ == 0 {
                                return v___y_4584_;
                            } else {
                                return v_suppressElabErrors_4585_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4599_ = crate::leanh::lean_ctor_get(v_pre_4588_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_4599_) == 0 {
                            let mut v_str_4600_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4601_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4602_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4603_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4604_: u8 = 0;
                            v_str_4600_ = crate::leanh::lean_ctor_get(v_x_4586_, 1);
                            v_str_4601_ = crate::leanh::lean_ctor_get(v_pre_4587_, 1);
                            v_str_4602_ = crate::leanh::lean_ctor_get(v_pre_4588_, 1);
                            v___x_4603_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3;
                            v___x_4604_ = lean_string_dec_eq(v_str_4602_, v___x_4603_);
                            if v___x_4604_ == 0 {
                                return v___y_4584_;
                            } else {
                                let mut v___x_4605_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4606_: u8 = 0;
                                v___x_4605_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4;
                                v___x_4606_ = lean_string_dec_eq(v_str_4601_, v___x_4605_);
                                if v___x_4606_ == 0 {
                                    return v___y_4584_;
                                } else {
                                    let mut v___x_4607_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4608_: u8 = 0;
                                    v___x_4607_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__5;
                                    v___x_4608_ = lean_string_dec_eq(v_str_4600_, v___x_4607_);
                                    if v___x_4608_ == 0 {
                                        return v___y_4584_;
                                    } else {
                                        return v_suppressElabErrors_4585_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4584_;
                        }
                    }
                    _ => {
                        return v___y_4584_;
                    }
                }
            }
            0 => {
                let mut v_str_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4611_: u8 = 0;
                v_str_4609_ = crate::leanh::lean_ctor_get(v_x_4586_, 1);
                v___x_4610_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__6;
                v___x_4611_ = lean_string_dec_eq(v_str_4609_, v___x_4610_);
                if v___x_4611_ == 0 {
                    return v___y_4584_;
                } else {
                    return v_suppressElabErrors_4585_;
                }
            }
            _ => {
                return v___y_4584_;
            }
        }
    } else {
        return v___y_4584_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___boxed(
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_4613_: *mut crate::leanh::LeanObject,
    mut v_x_4614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_20920__boxed_4615_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4616_: u8 = 0;
    let mut v_res_4617_: u8 = 0;
    let mut v_r_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_20920__boxed_4615_ = (crate::leanh::lean_unbox(v___y_4612_) as u8);
    v_suppressElabErrors_boxed_4616_ = (crate::leanh::lean_unbox(v_suppressElabErrors_4613_) as u8);
    v_res_4617_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0(v___y_20920__boxed_4615_, v_suppressElabErrors_boxed_4616_, v_x_4614_);
    crate::leanh::lean_dec(v_x_4614_);
    v_r_4618_ = crate::leanh::lean_box((v_res_4617_) as usize);
    return v_r_4618_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(
    mut v_ref_4620_: *mut crate::leanh::LeanObject,
    mut v_msgData_4621_: *mut crate::leanh::LeanObject,
    mut v_severity_4622_: u8,
    mut v_isSilent_4623_: u8,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4630_: u8 = 0;
    let mut v___y_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4632_: u8 = 0;
    let mut v___y_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v___y_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4667_: u8 = 0;
    let mut v___y_4668_: u8 = 0;
    let mut v___y_4669_: u8 = 0;
    let mut v___y_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4679_: u8 = 0;
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v___y_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4692_: u8 = 0;
    let mut v___y_4693_: u8 = 0;
    let mut v___y_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4695_: u8 = 0;
    let mut v___y_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4704_: u8 = 0;
    let mut v___y_4705_: u8 = 0;
    let mut v___y_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4708_: u8 = 0;
    let mut v_ref_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___y_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4717_: u8 = 0;
    let mut v___y_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4720_: u8 = 0;
    let mut v___y_4721_: u8 = 0;
    let mut v___y_4723_: u8 = 0;
    let mut v_fileName_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4728_: u8 = 0;
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: u8 = 0;
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: u8 = 0;
    let mut v___x_4739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4713_ = 2;
                v___x_4738_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4622_, v___x_4713_);
                if v___x_4738_ == 0 {
                    v___y_4723_ = v___x_4738_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_4621_);
                    v___x_4739_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4621_);
                    v___y_4723_ = v___x_4739_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4639_ = lean_st_ref_take(v___y_4638_);
                v_currNamespace_4640_ = crate::leanh::lean_ctor_get(v___y_4637_, 6);
                v_openDecls_4641_ = crate::leanh::lean_ctor_get(v___y_4637_, 7);
                v_env_4642_ = crate::leanh::lean_ctor_get(v___x_4639_, 0);
                v_nextMacroScope_4643_ = crate::leanh::lean_ctor_get(v___x_4639_, 1);
                v_ngen_4644_ = crate::leanh::lean_ctor_get(v___x_4639_, 2);
                v_auxDeclNGen_4645_ = crate::leanh::lean_ctor_get(v___x_4639_, 3);
                v_traceState_4646_ = crate::leanh::lean_ctor_get(v___x_4639_, 4);
                v_cache_4647_ = crate::leanh::lean_ctor_get(v___x_4639_, 5);
                v_messages_4648_ = crate::leanh::lean_ctor_get(v___x_4639_, 6);
                v_infoState_4649_ = crate::leanh::lean_ctor_get(v___x_4639_, 7);
                v_snapshotTasks_4650_ = crate::leanh::lean_ctor_get(v___x_4639_, 8);
                v_isSharedCheck_4664_ = (!crate::leanh::lean_is_exclusive(v___x_4639_)) as u8;
                if v_isSharedCheck_4664_ == 0 {
                    v___x_4652_ = v___x_4639_;
                    v_isShared_4653_ = v_isSharedCheck_4664_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4650_);
                    crate::leanh::lean_inc(v_infoState_4649_);
                    crate::leanh::lean_inc(v_messages_4648_);
                    crate::leanh::lean_inc(v_cache_4647_);
                    crate::leanh::lean_inc(v_traceState_4646_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4645_);
                    crate::leanh::lean_inc(v_ngen_4644_);
                    crate::leanh::lean_inc(v_nextMacroScope_4643_);
                    crate::leanh::lean_inc(v_env_4642_);
                    crate::leanh::lean_dec(v___x_4639_);
                    v___x_4652_ = crate::leanh::lean_box(0);
                    v_isShared_4653_ = v_isSharedCheck_4664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_4641_);
                crate::leanh::lean_inc(v_currNamespace_4640_);
                v___x_4654_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4654_, 0, v_currNamespace_4640_);
                crate::leanh::lean_ctor_set(v___x_4654_, 1, v_openDecls_4641_);
                v___x_4655_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4655_, 0, v___x_4654_);
                crate::leanh::lean_ctor_set(v___x_4655_, 1, v___y_4635_);
                crate::leanh::lean_inc_ref(v___y_4633_);
                crate::leanh::lean_inc_ref(v___y_4634_);
                v___x_4656_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_4656_, 0, v___y_4634_);
                crate::leanh::lean_ctor_set(v___x_4656_, 1, v___y_4636_);
                crate::leanh::lean_ctor_set(v___x_4656_, 2, v___y_4631_);
                crate::leanh::lean_ctor_set(v___x_4656_, 3, v___y_4633_);
                crate::leanh::lean_ctor_set(v___x_4656_, 4, v___x_4655_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_4630_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4632_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4623_,
                );
                v___x_4657_ = l_Lean_MessageLog_add(v___x_4656_, v_messages_4648_);
                if v_isShared_4653_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4652_, 6, v___x_4657_);
                    v___x_4659_ = v___x_4652_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4663_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_env_4642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_nextMacroScope_4643_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_ngen_4644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 3, v_auxDeclNGen_4645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 4, v_traceState_4646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 5, v_cache_4647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 6, v___x_4657_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 7, v_infoState_4649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4663_, 8, v_snapshotTasks_4650_);
                    v___x_4659_ = v_reuseFailAlloc_4663_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4660_ = lean_st_ref_set(v___y_4638_, v___x_4659_);
                v___x_4661_ = crate::leanh::lean_box(0);
                v___x_4662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4662_, 0, v___x_4661_);
                return v___x_4662_;
            }
            4 => {
                v___x_4674_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4621_,
                    );
                v___x_4675_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v___x_4674_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
                v_a_4676_ = crate::leanh::lean_ctor_get(v___x_4675_, 0);
                v_isSharedCheck_4689_ = (!crate::leanh::lean_is_exclusive(v___x_4675_)) as u8;
                if v_isSharedCheck_4689_ == 0 {
                    v___x_4678_ = v___x_4675_;
                    v_isShared_4679_ = v_isSharedCheck_4689_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4676_);
                    crate::leanh::lean_dec(v___x_4675_);
                    v___x_4678_ = crate::leanh::lean_box(0);
                    v_isShared_4679_ = v_isSharedCheck_4689_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_4671_, 2);
                v___x_4680_ = l_Lean_FileMap_toPosition(v___y_4671_, v___y_4672_);
                crate::leanh::lean_dec(v___y_4672_);
                v___x_4681_ = l_Lean_FileMap_toPosition(v___y_4671_, v___y_4673_);
                crate::leanh::lean_dec(v___y_4673_);
                v___x_4682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4682_, 0, v___x_4681_);
                v___x_4683_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0;
                if v___y_4668_ == 0 {
                    crate::leanh::lean_del_object(v___x_4678_);
                    crate::leanh::lean_dec_ref(v___y_4666_);
                    v___y_4630_ = v___y_4667_;
                    v___y_4631_ = v___x_4682_;
                    v___y_4632_ = v___y_4669_;
                    v___y_4633_ = v___x_4683_;
                    v___y_4634_ = v___y_4670_;
                    v___y_4635_ = v_a_4676_;
                    v___y_4636_ = v___x_4680_;
                    v___y_4637_ = v___y_4626_;
                    v___y_4638_ = v___y_4627_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4676_);
                    v___x_4684_ = l_Lean_MessageData_hasTag(v___y_4666_, v_a_4676_);
                    if v___x_4684_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4682_, 1);
                        crate::leanh::lean_dec_ref(v___x_4680_);
                        crate::leanh::lean_dec(v_a_4676_);
                        v___x_4685_ = crate::leanh::lean_box(0);
                        if v_isShared_4679_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4678_, 0, v___x_4685_);
                            v___x_4687_ = v___x_4678_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4688_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
                            v___x_4687_ = v_reuseFailAlloc_4688_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4678_);
                        v___y_4630_ = v___y_4667_;
                        v___y_4631_ = v___x_4682_;
                        v___y_4632_ = v___y_4669_;
                        v___y_4633_ = v___x_4683_;
                        v___y_4634_ = v___y_4670_;
                        v___y_4635_ = v_a_4676_;
                        v___y_4636_ = v___x_4680_;
                        v___y_4637_ = v___y_4626_;
                        v___y_4638_ = v___y_4627_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4687_;
            }
            7 => {
                v___x_4699_ = l_Lean_Syntax_getTailPos_x3f(v___y_4694_, v___y_4692_);
                crate::leanh::lean_dec(v___y_4694_);
                if crate::leanh::lean_obj_tag(v___x_4699_) == 0 {
                    crate::leanh::lean_inc(v___y_4698_);
                    v___y_4666_ = v___y_4691_;
                    v___y_4667_ = v___y_4692_;
                    v___y_4668_ = v___y_4693_;
                    v___y_4669_ = v___y_4695_;
                    v___y_4670_ = v___y_4696_;
                    v___y_4671_ = v___y_4697_;
                    v___y_4672_ = v___y_4698_;
                    v___y_4673_ = v___y_4698_;
                    state = 4;
                    continue;
                } else {
                    v_val_4700_ = crate::leanh::lean_ctor_get(v___x_4699_, 0);
                    crate::leanh::lean_inc(v_val_4700_);
                    crate::leanh::lean_dec_ref_known(v___x_4699_, 1);
                    v___y_4666_ = v___y_4691_;
                    v___y_4667_ = v___y_4692_;
                    v___y_4668_ = v___y_4693_;
                    v___y_4669_ = v___y_4695_;
                    v___y_4670_ = v___y_4696_;
                    v___y_4671_ = v___y_4697_;
                    v___y_4672_ = v___y_4698_;
                    v___y_4673_ = v_val_4700_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4709_ = l_Lean_replaceRef(v_ref_4620_, v___y_4703_);
                v___x_4710_ = l_Lean_Syntax_getPos_x3f(v_ref_4709_, v___y_4704_);
                if crate::leanh::lean_obj_tag(v___x_4710_) == 0 {
                    v___x_4711_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4691_ = v___y_4702_;
                    v___y_4692_ = v___y_4704_;
                    v___y_4693_ = v___y_4705_;
                    v___y_4694_ = v_ref_4709_;
                    v___y_4695_ = v___y_4708_;
                    v___y_4696_ = v___y_4706_;
                    v___y_4697_ = v___y_4707_;
                    v___y_4698_ = v___x_4711_;
                    state = 7;
                    continue;
                } else {
                    v_val_4712_ = crate::leanh::lean_ctor_get(v___x_4710_, 0);
                    crate::leanh::lean_inc(v_val_4712_);
                    crate::leanh::lean_dec_ref_known(v___x_4710_, 1);
                    v___y_4691_ = v___y_4702_;
                    v___y_4692_ = v___y_4704_;
                    v___y_4693_ = v___y_4705_;
                    v___y_4694_ = v_ref_4709_;
                    v___y_4695_ = v___y_4708_;
                    v___y_4696_ = v___y_4706_;
                    v___y_4697_ = v___y_4707_;
                    v___y_4698_ = v_val_4712_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4721_ == 0 {
                    v___y_4702_ = v___y_4716_;
                    v___y_4703_ = v___y_4715_;
                    v___y_4704_ = v___y_4720_;
                    v___y_4705_ = v___y_4717_;
                    v___y_4706_ = v___y_4718_;
                    v___y_4707_ = v___y_4719_;
                    v___y_4708_ = v_severity_4622_;
                    state = 8;
                    continue;
                } else {
                    v___y_4702_ = v___y_4716_;
                    v___y_4703_ = v___y_4715_;
                    v___y_4704_ = v___y_4720_;
                    v___y_4705_ = v___y_4717_;
                    v___y_4706_ = v___y_4718_;
                    v___y_4707_ = v___y_4719_;
                    v___y_4708_ = v___x_4713_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4723_ == 0 {
                    v_fileName_4724_ = crate::leanh::lean_ctor_get(v___y_4626_, 0);
                    v_fileMap_4725_ = crate::leanh::lean_ctor_get(v___y_4626_, 1);
                    v_options_4726_ = crate::leanh::lean_ctor_get(v___y_4626_, 2);
                    v_ref_4727_ = crate::leanh::lean_ctor_get(v___y_4626_, 5);
                    v_suppressElabErrors_4728_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4626_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4729_ = crate::leanh::lean_box((v___y_4723_) as usize);
                    v___x_4730_ = crate::leanh::lean_box((v_suppressElabErrors_4728_) as usize);
                    v___f_4731_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_4731_, 0, v___x_4729_);
                    crate::leanh::lean_closure_set(v___f_4731_, 1, v___x_4730_);
                    v___x_4732_ = 1;
                    v___x_4733_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4622_, v___x_4732_);
                    if v___x_4733_ == 0 {
                        v___y_4715_ = v_ref_4727_;
                        v___y_4716_ = v___f_4731_;
                        v___y_4717_ = v_suppressElabErrors_4728_;
                        v___y_4718_ = v_fileName_4724_;
                        v___y_4719_ = v_fileMap_4725_;
                        v___y_4720_ = v___y_4723_;
                        v___y_4721_ = v___x_4733_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4734_ = l_Lean_warningAsError;
                        v___x_4735_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_4726_, v___x_4734_);
                        v___y_4715_ = v_ref_4727_;
                        v___y_4716_ = v___f_4731_;
                        v___y_4717_ = v_suppressElabErrors_4728_;
                        v___y_4718_ = v_fileName_4724_;
                        v___y_4719_ = v_fileMap_4725_;
                        v___y_4720_ = v___y_4723_;
                        v___y_4721_ = v___x_4735_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_4621_);
                    v___x_4736_ = crate::leanh::lean_box(0);
                    v___x_4737_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4737_, 0, v___x_4736_);
                    return v___x_4737_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___boxed(
    mut v_ref_4740_: *mut crate::leanh::LeanObject,
    mut v_msgData_4741_: *mut crate::leanh::LeanObject,
    mut v_severity_4742_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
    mut v___y_4748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4749_: u8 = 0;
    let mut v_isSilent_boxed_4750_: u8 = 0;
    let mut v_res_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4749_ = (crate::leanh::lean_unbox(v_severity_4742_) as u8);
    v_isSilent_boxed_4750_ = (crate::leanh::lean_unbox(v_isSilent_4743_) as u8);
    v_res_4751_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(v_ref_4740_, v_msgData_4741_, v_severity_boxed_4749_, v_isSilent_boxed_4750_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
    crate::leanh::lean_dec(v___y_4747_);
    crate::leanh::lean_dec_ref(v___y_4746_);
    crate::leanh::lean_dec(v___y_4745_);
    crate::leanh::lean_dec_ref(v___y_4744_);
    crate::leanh::lean_dec(v_ref_4740_);
    return v_res_4751_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9(
    mut v_msgData_4752_: *mut crate::leanh::LeanObject,
    mut v_severity_4753_: u8,
    mut v_isSilent_4754_: u8,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
    mut v___y_4758_: *mut crate::leanh::LeanObject,
    mut v___y_4759_: *mut crate::leanh::LeanObject,
    mut v___y_4760_: *mut crate::leanh::LeanObject,
    mut v___y_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4764_ = crate::leanh::lean_ctor_get(v___y_4761_, 5);
    v___x_4765_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(v_ref_4764_, v_msgData_4752_, v_severity_4753_, v_isSilent_4754_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
    return v___x_4765_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9___boxed(
    mut v_msgData_4766_: *mut crate::leanh::LeanObject,
    mut v_severity_4767_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4768_: *mut crate::leanh::LeanObject,
    mut v___y_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
    mut v___y_4772_: *mut crate::leanh::LeanObject,
    mut v___y_4773_: *mut crate::leanh::LeanObject,
    mut v___y_4774_: *mut crate::leanh::LeanObject,
    mut v___y_4775_: *mut crate::leanh::LeanObject,
    mut v___y_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4778_: u8 = 0;
    let mut v_isSilent_boxed_4779_: u8 = 0;
    let mut v_res_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4778_ = (crate::leanh::lean_unbox(v_severity_4767_) as u8);
    v_isSilent_boxed_4779_ = (crate::leanh::lean_unbox(v_isSilent_4768_) as u8);
    v_res_4780_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9(v_msgData_4766_, v_severity_boxed_4778_, v_isSilent_boxed_4779_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
    crate::leanh::lean_dec(v___y_4776_);
    crate::leanh::lean_dec_ref(v___y_4775_);
    crate::leanh::lean_dec(v___y_4774_);
    crate::leanh::lean_dec_ref(v___y_4773_);
    crate::leanh::lean_dec(v___y_4772_);
    crate::leanh::lean_dec_ref(v___y_4771_);
    crate::leanh::lean_dec(v___y_4770_);
    crate::leanh::lean_dec_ref(v___y_4769_);
    return v_res_4780_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9(
    mut v_msgData_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
    mut v___y_4786_: *mut crate::leanh::LeanObject,
    mut v___y_4787_: *mut crate::leanh::LeanObject,
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v___y_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: u8 = 0;
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4791_ = 2;
    v___x_4792_ = 0;
    v___x_4793_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9(v_msgData_4781_, v___x_4791_, v___x_4792_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_);
    return v___x_4793_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9___boxed(
    mut v_msgData_4794_: *mut crate::leanh::LeanObject,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
    mut v___y_4801_: *mut crate::leanh::LeanObject,
    mut v___y_4802_: *mut crate::leanh::LeanObject,
    mut v___y_4803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4804_ = l_Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9(
        v_msgData_4794_,
        v___y_4795_,
        v___y_4796_,
        v___y_4797_,
        v___y_4798_,
        v___y_4799_,
        v___y_4800_,
        v___y_4801_,
        v___y_4802_,
    );
    crate::leanh::lean_dec(v___y_4802_);
    crate::leanh::lean_dec_ref(v___y_4801_);
    crate::leanh::lean_dec(v___y_4800_);
    crate::leanh::lean_dec_ref(v___y_4799_);
    crate::leanh::lean_dec(v___y_4798_);
    crate::leanh::lean_dec_ref(v___y_4797_);
    crate::leanh::lean_dec(v___y_4796_);
    crate::leanh::lean_dec_ref(v___y_4795_);
    return v_res_4804_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__3(
    mut v_a_4805_: *mut crate::leanh::LeanObject,
    mut v_a_4806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4812_: u8 = 0;
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4805_) == 0 {
                    v___x_4807_ = l_List_reverse___redArg(v_a_4806_);
                    return v___x_4807_;
                } else {
                    v_head_4808_ = crate::leanh::lean_ctor_get(v_a_4805_, 0);
                    v_tail_4809_ = crate::leanh::lean_ctor_get(v_a_4805_, 1);
                    v_isSharedCheck_4818_ = (!crate::leanh::lean_is_exclusive(v_a_4805_)) as u8;
                    if v_isSharedCheck_4818_ == 0 {
                        v___x_4811_ = v_a_4805_;
                        v_isShared_4812_ = v_isSharedCheck_4818_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4809_);
                        crate::leanh::lean_inc(v_head_4808_);
                        crate::leanh::lean_dec(v_a_4805_);
                        v___x_4811_ = crate::leanh::lean_box(0);
                        v_isShared_4812_ = v_isSharedCheck_4818_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4813_ = l_Lean_Expr_fvar___override(v_head_4808_);
                if v_isShared_4812_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4811_, 1, v_a_4806_);
                    crate::leanh::lean_ctor_set(v___x_4811_, 0, v___x_4813_);
                    v___x_4815_ = v___x_4811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4817_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4813_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_a_4806_);
                    v___x_4815_ = v_reuseFailAlloc_4817_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4805_ = v_tail_4809_;
                v_a_4806_ = v___x_4815_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__2(
    mut v_sz_4819_: usize,
    mut v_i_4820_: usize,
    mut v_bs_4821_: *mut crate::leanh::LeanObject,
    mut v___y_4822_: *mut crate::leanh::LeanObject,
    mut v___y_4823_: *mut crate::leanh::LeanObject,
    mut v___y_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: u8 = 0;
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: usize = 0;
    let mut v___x_4839_: usize = 0;
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4845_: u8 = 0;
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4831_ = lean_usize_dec_lt(v_i_4820_, v_sz_4819_);
                if v___x_4831_ == 0 {
                    v___x_4832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4832_, 0, v_bs_4821_);
                    return v___x_4832_;
                } else {
                    v_v_4833_ = lean_array_uget_borrowed(v_bs_4821_, v_i_4820_);
                    crate::leanh::lean_inc(v_v_4833_);
                    v___x_4834_ = l_Lean_Elab_Tactic_getFVarId(
                        v_v_4833_,
                        v___y_4822_,
                        v___y_4823_,
                        v___y_4824_,
                        v___y_4825_,
                        v___y_4826_,
                        v___y_4827_,
                        v___y_4828_,
                        v___y_4829_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4834_) == 0 {
                        v_a_4835_ = crate::leanh::lean_ctor_get(v___x_4834_, 0);
                        crate::leanh::lean_inc(v_a_4835_);
                        crate::leanh::lean_dec_ref_known(v___x_4834_, 1);
                        v___x_4836_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4837_ = lean_array_uset(v_bs_4821_, v_i_4820_, v___x_4836_);
                        v___x_4838_ = 1usize;
                        v___x_4839_ = lean_usize_add(v_i_4820_, v___x_4838_);
                        v___x_4840_ = lean_array_uset(v_bs_x27_4837_, v_i_4820_, v_a_4835_);
                        v_i_4820_ = v___x_4839_;
                        v_bs_4821_ = v___x_4840_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4821_);
                        v_a_4842_ = crate::leanh::lean_ctor_get(v___x_4834_, 0);
                        v_isSharedCheck_4849_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4834_)) as u8;
                        if v_isSharedCheck_4849_ == 0 {
                            v___x_4844_ = v___x_4834_;
                            v_isShared_4845_ = v_isSharedCheck_4849_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4842_);
                            crate::leanh::lean_dec(v___x_4834_);
                            v___x_4844_ = crate::leanh::lean_box(0);
                            v_isShared_4845_ = v_isSharedCheck_4849_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4845_ == 0 {
                    v___x_4847_ = v___x_4844_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
                    v___x_4847_ = v_reuseFailAlloc_4848_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__2___boxed(
    mut v_sz_4850_: *mut crate::leanh::LeanObject,
    mut v_i_4851_: *mut crate::leanh::LeanObject,
    mut v_bs_4852_: *mut crate::leanh::LeanObject,
    mut v___y_4853_: *mut crate::leanh::LeanObject,
    mut v___y_4854_: *mut crate::leanh::LeanObject,
    mut v___y_4855_: *mut crate::leanh::LeanObject,
    mut v___y_4856_: *mut crate::leanh::LeanObject,
    mut v___y_4857_: *mut crate::leanh::LeanObject,
    mut v___y_4858_: *mut crate::leanh::LeanObject,
    mut v___y_4859_: *mut crate::leanh::LeanObject,
    mut v___y_4860_: *mut crate::leanh::LeanObject,
    mut v___y_4861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4862_: usize = 0;
    let mut v_i_boxed_4863_: usize = 0;
    let mut v_res_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4862_ = crate::leanh::lean_unbox_usize(v_sz_4850_);
    crate::leanh::lean_dec(v_sz_4850_);
    v_i_boxed_4863_ = crate::leanh::lean_unbox_usize(v_i_4851_);
    crate::leanh::lean_dec(v_i_4851_);
    v_res_4864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__2(v_sz_boxed_4862_, v_i_boxed_4863_, v_bs_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
    crate::leanh::lean_dec(v___y_4860_);
    crate::leanh::lean_dec_ref(v___y_4859_);
    crate::leanh::lean_dec(v___y_4858_);
    crate::leanh::lean_dec_ref(v___y_4857_);
    crate::leanh::lean_dec(v___y_4856_);
    crate::leanh::lean_dec_ref(v___y_4855_);
    crate::leanh::lean_dec(v___y_4854_);
    crate::leanh::lean_dec_ref(v___y_4853_);
    return v_res_4864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___lam__0(
    mut v___x_4865_: *mut crate::leanh::LeanObject,
    mut v___y_4866_: *mut crate::leanh::LeanObject,
    mut v___y_4867_: *mut crate::leanh::LeanObject,
    mut v___y_4868_: *mut crate::leanh::LeanObject,
    mut v___y_4869_: *mut crate::leanh::LeanObject,
    mut v___y_4870_: *mut crate::leanh::LeanObject,
    mut v___y_4871_: *mut crate::leanh::LeanObject,
    mut v___y_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4879_: u8 = 0;
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4875_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(v___x_4865_, v___y_4871_);
                if crate::leanh::lean_obj_tag(v___x_4875_) == 0 {
                    v_a_4876_ = crate::leanh::lean_ctor_get(v___x_4875_, 0);
                    v_isSharedCheck_4884_ = (!crate::leanh::lean_is_exclusive(v___x_4875_)) as u8;
                    if v_isSharedCheck_4884_ == 0 {
                        v___x_4878_ = v___x_4875_;
                        v_isShared_4879_ = v_isSharedCheck_4884_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4876_);
                        crate::leanh::lean_dec(v___x_4875_);
                        v___x_4878_ = crate::leanh::lean_box(0);
                        v_isShared_4879_ = v_isSharedCheck_4884_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_4875_;
                }
            }
            1 => {
                v___x_4880_ = l_Lean_Expr_headBeta(v_a_4876_);
                if v_isShared_4879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4878_, 0, v___x_4880_);
                    v___x_4882_ = v___x_4878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4883_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
                    v___x_4882_ = v_reuseFailAlloc_4883_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4882_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___lam__0___boxed(
    mut v___x_4885_: *mut crate::leanh::LeanObject,
    mut v___y_4886_: *mut crate::leanh::LeanObject,
    mut v___y_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
    mut v___y_4893_: *mut crate::leanh::LeanObject,
    mut v___y_4894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___lam__0(v___x_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
    crate::leanh::lean_dec(v___y_4893_);
    crate::leanh::lean_dec_ref(v___y_4892_);
    crate::leanh::lean_dec(v___y_4891_);
    crate::leanh::lean_dec_ref(v___y_4890_);
    crate::leanh::lean_dec(v___y_4889_);
    crate::leanh::lean_dec_ref(v___y_4888_);
    crate::leanh::lean_dec(v___y_4887_);
    crate::leanh::lean_dec_ref(v___y_4886_);
    return v_res_4895_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10(
    mut v_a_4896_: *mut crate::leanh::LeanObject,
    mut v_sz_4897_: usize,
    mut v_i_4898_: usize,
    mut v_bs_4899_: *mut crate::leanh::LeanObject,
    mut v___y_4900_: *mut crate::leanh::LeanObject,
    mut v___y_4901_: *mut crate::leanh::LeanObject,
    mut v___y_4902_: *mut crate::leanh::LeanObject,
    mut v___y_4903_: *mut crate::leanh::LeanObject,
    mut v___y_4904_: *mut crate::leanh::LeanObject,
    mut v___y_4905_: *mut crate::leanh::LeanObject,
    mut v___y_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4909_: u8 = 0;
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: usize = 0;
    let mut v___x_4920_: usize = 0;
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4926_: u8 = 0;
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4909_ = lean_usize_dec_lt(v_i_4898_, v_sz_4897_);
                if v___x_4909_ == 0 {
                    crate::leanh::lean_dec(v_a_4896_);
                    v___x_4910_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4910_, 0, v_bs_4899_);
                    return v___x_4910_;
                } else {
                    v_v_4911_ = lean_array_uget_borrowed(v_bs_4899_, v_i_4898_);
                    v_snd_4912_ = crate::leanh::lean_ctor_get(v_v_4911_, 1);
                    crate::leanh::lean_inc(v_a_4896_);
                    v___x_4913_ = l_Lean_mkMVar(v_a_4896_);
                    v___f_4914_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                    crate::leanh::lean_closure_set(v___f_4914_, 0, v___x_4913_);
                    crate::leanh::lean_inc(v_snd_4912_);
                    v___x_4915_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(v_snd_4912_, v___f_4914_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
                    if crate::leanh::lean_obj_tag(v___x_4915_) == 0 {
                        v_a_4916_ = crate::leanh::lean_ctor_get(v___x_4915_, 0);
                        crate::leanh::lean_inc(v_a_4916_);
                        crate::leanh::lean_dec_ref_known(v___x_4915_, 1);
                        v___x_4917_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4918_ = lean_array_uset(v_bs_4899_, v_i_4898_, v___x_4917_);
                        v___x_4919_ = 1usize;
                        v___x_4920_ = lean_usize_add(v_i_4898_, v___x_4919_);
                        v___x_4921_ = lean_array_uset(v_bs_x27_4918_, v_i_4898_, v_a_4916_);
                        v_i_4898_ = v___x_4920_;
                        v_bs_4899_ = v___x_4921_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4899_);
                        crate::leanh::lean_dec(v_a_4896_);
                        v_a_4923_ = crate::leanh::lean_ctor_get(v___x_4915_, 0);
                        v_isSharedCheck_4930_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4915_)) as u8;
                        if v_isSharedCheck_4930_ == 0 {
                            v___x_4925_ = v___x_4915_;
                            v_isShared_4926_ = v_isSharedCheck_4930_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4923_);
                            crate::leanh::lean_dec(v___x_4915_);
                            v___x_4925_ = crate::leanh::lean_box(0);
                            v_isShared_4926_ = v_isSharedCheck_4930_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4926_ == 0 {
                    v___x_4928_ = v___x_4925_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4929_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
                    v___x_4928_ = v_reuseFailAlloc_4929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___boxed(
    mut v_a_4931_: *mut crate::leanh::LeanObject,
    mut v_sz_4932_: *mut crate::leanh::LeanObject,
    mut v_i_4933_: *mut crate::leanh::LeanObject,
    mut v_bs_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
    mut v___y_4936_: *mut crate::leanh::LeanObject,
    mut v___y_4937_: *mut crate::leanh::LeanObject,
    mut v___y_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4944_: usize = 0;
    let mut v_i_boxed_4945_: usize = 0;
    let mut v_res_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4944_ = crate::leanh::lean_unbox_usize(v_sz_4932_);
    crate::leanh::lean_dec(v_sz_4932_);
    v_i_boxed_4945_ = crate::leanh::lean_unbox_usize(v_i_4933_);
    crate::leanh::lean_dec(v_i_4933_);
    v_res_4946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10(v_a_4931_, v_sz_boxed_4944_, v_i_boxed_4945_, v_bs_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
    crate::leanh::lean_dec(v___y_4942_);
    crate::leanh::lean_dec_ref(v___y_4941_);
    crate::leanh::lean_dec(v___y_4940_);
    crate::leanh::lean_dec_ref(v___y_4939_);
    crate::leanh::lean_dec(v___y_4938_);
    crate::leanh::lean_dec_ref(v___y_4937_);
    crate::leanh::lean_dec(v___y_4936_);
    crate::leanh::lean_dec_ref(v___y_4935_);
    return v_res_4946_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4954_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3;
    v___x_4955_ = l_Lean_MessageData_ofFormat(v___x_4954_);
    return v___x_4955_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4960_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7;
    v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
    return v___x_4961_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__2(
    mut v___y_4963_: *mut crate::leanh::LeanObject,
    mut v_config_4964_: *mut crate::leanh::LeanObject,
    mut v_snd_4965_: *mut crate::leanh::LeanObject,
    mut v_a_4966_: *mut crate::leanh::LeanObject,
    mut v_a_4967_: *mut crate::leanh::LeanObject,
    mut v_ref_4968_: *mut crate::leanh::LeanObject,
    mut v_requireClose_4969_: u8,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
    mut v___y_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
    mut v___y_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4986_: usize = 0;
    let mut v___x_4987_: usize = 0;
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_grind_4990_: u8 = 0;
    let mut v_try_x3f_4991_: u8 = 0;
    let mut v_star_4992_: u8 = 0;
    let mut v_all_4993_: u8 = 0;
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5009_: u8 = 0;
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: u8 = 0;
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_val_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5021_: u8 = 0;
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5024_: usize = 0;
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5030_: u8 = 0;
    let mut v___y_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5041_: usize = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: u8 = 0;
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5059_: usize = 0;
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5073_: u8 = 0;
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5077_: u8 = 0;
    let mut v___y_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: u8 = 0;
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: u8 = 0;
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: u8 = 0;
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5119_: u8 = 0;
    let mut v_isSharedCheck_5120_: u8 = 0;
    let mut v_a_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5124_: u8 = 0;
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5128_: u8 = 0;
    let mut v_a_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5132_: u8 = 0;
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4986_ = lean_array_size(v___y_4963_);
                v___x_4987_ = 0usize;
                v___x_4988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__2(v_sz_4986_, v___x_4987_, v___y_4963_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
                if crate::leanh::lean_obj_tag(v___x_4988_) == 0 {
                    v_a_4989_ = crate::leanh::lean_ctor_get(v___x_4988_, 0);
                    crate::leanh::lean_inc(v_a_4989_);
                    crate::leanh::lean_dec_ref_known(v___x_4988_, 1);
                    v_grind_4990_ = crate::leanh::lean_ctor_get_uint8(v_config_4964_, 0 as u32);
                    v_try_x3f_4991_ = crate::leanh::lean_ctor_get_uint8(v_config_4964_, 1 as u32);
                    v_star_4992_ = crate::leanh::lean_ctor_get_uint8(v_config_4964_, 2 as u32);
                    v_all_4993_ = crate::leanh::lean_ctor_get_uint8(v_config_4964_, 3 as u32);
                    v___x_4994_ = lean_array_to_list(v_a_4989_);
                    v___x_4995_ = crate::leanh::lean_box(0);
                    v___x_4996_ =
                        l_List_mapTR_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__3(
                            v___x_4994_,
                            v___x_4995_,
                        );
                    v___x_4997_ = crate::leanh::lean_box((v_grind_4990_) as usize);
                    v___x_4998_ = crate::leanh::lean_box((v_try_x3f_4991_) as usize);
                    crate::leanh::lean_inc(v___x_4996_);
                    v___f_4999_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_4999_, 0, v___x_4996_);
                    crate::leanh::lean_closure_set(v___f_4999_, 1, v___x_4997_);
                    crate::leanh::lean_closure_set(v___f_4999_, 2, v___x_4998_);
                    v___f_5000_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5000_, 0, v___x_4996_);
                    v___x_5001_ = crate::leanh::lean_unsigned_to_nat(10);
                    crate::leanh::lean_inc(v_snd_4965_);
                    v___x_5002_ = l_Lean_Meta_LibrarySearch_librarySearch(
                        v_snd_4965_,
                        v___f_4999_,
                        v___f_5000_,
                        v___x_5001_,
                        v_star_4992_,
                        v_all_4993_,
                        v___y_4974_,
                        v___y_4975_,
                        v___y_4976_,
                        v___y_4977_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5002_) == 0 {
                        v_a_5003_ = crate::leanh::lean_ctor_get(v___x_5002_, 0);
                        crate::leanh::lean_inc(v_a_5003_);
                        crate::leanh::lean_dec_ref_known(v___x_5002_, 1);
                        if crate::leanh::lean_obj_tag(v_a_5003_) == 0 {
                            crate::leanh::lean_dec(v_snd_4965_);
                            v___x_5004_ = l_Lean_mkMVar(v_a_4966_);
                            v___x_5005_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(v___x_5004_, v___y_4975_);
                            v_a_5006_ = crate::leanh::lean_ctor_get(v___x_5005_, 0);
                            v_isSharedCheck_5017_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5005_)) as u8;
                            if v_isSharedCheck_5017_ == 0 {
                                v___x_5008_ = v___x_5005_;
                                v_isShared_5009_ = v_isSharedCheck_5017_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5006_);
                                crate::leanh::lean_dec(v___x_5005_);
                                v___x_5008_ = crate::leanh::lean_box(0);
                                v_isShared_5009_ = v_isSharedCheck_5017_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_val_5018_ = crate::leanh::lean_ctor_get(v_a_5003_, 0);
                            v_isSharedCheck_5120_ =
                                (!crate::leanh::lean_is_exclusive(v_a_5003_)) as u8;
                            if v_isSharedCheck_5120_ == 0 {
                                v___x_5020_ = v_a_5003_;
                                v_isShared_5021_ = v_isSharedCheck_5120_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_5018_);
                                crate::leanh::lean_dec(v_a_5003_);
                                v___x_5020_ = crate::leanh::lean_box(0);
                                v_isShared_5021_ = v_isSharedCheck_5120_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_ref_4968_);
                        crate::leanh::lean_dec_ref(v_a_4967_);
                        crate::leanh::lean_dec(v_a_4966_);
                        crate::leanh::lean_dec(v_snd_4965_);
                        v_a_5121_ = crate::leanh::lean_ctor_get(v___x_5002_, 0);
                        v_isSharedCheck_5128_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5002_)) as u8;
                        if v_isSharedCheck_5128_ == 0 {
                            v___x_5123_ = v___x_5002_;
                            v_isShared_5124_ = v_isSharedCheck_5128_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5121_);
                            crate::leanh::lean_dec(v___x_5002_);
                            v___x_5123_ = crate::leanh::lean_box(0);
                            v_isShared_5124_ = v_isSharedCheck_5128_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_ref_4968_);
                    crate::leanh::lean_dec_ref(v_a_4967_);
                    crate::leanh::lean_dec(v_a_4966_);
                    crate::leanh::lean_dec(v_snd_4965_);
                    v_a_5129_ = crate::leanh::lean_ctor_get(v___x_4988_, 0);
                    v_isSharedCheck_5136_ = (!crate::leanh::lean_is_exclusive(v___x_4988_)) as u8;
                    if v_isSharedCheck_5136_ == 0 {
                        v___x_5131_ = v___x_4988_;
                        v_isShared_5132_ = v_isSharedCheck_5136_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5129_);
                        crate::leanh::lean_dec(v___x_4988_);
                        v___x_5131_ = crate::leanh::lean_box(0);
                        v_isShared_5132_ = v_isSharedCheck_5136_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4984_ = 0;
                v___x_4985_ = l_Lean_Elab_admitGoal(
                    v_snd_4965_,
                    v___x_4984_,
                    v___y_4980_,
                    v___y_4981_,
                    v___y_4982_,
                    v___y_4983_,
                );
                return v___x_4985_;
            }
            2 => {
                v___x_5010_ = l_Lean_Expr_headBeta(v_a_5006_);
                v___x_5011_ = crate::leanh::lean_box(0);
                v___x_5012_ = 0;
                if v_isShared_5009_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5008_, 1);
                    crate::leanh::lean_ctor_set(v___x_5008_, 0, v_a_4967_);
                    v___x_5014_ = v___x_5008_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_4967_);
                    v___x_5014_ = v_reuseFailAlloc_5016_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5015_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestion(
                    v_ref_4968_,
                    v___x_5010_,
                    v___x_5011_,
                    v___x_5012_,
                    v___x_5011_,
                    v___x_5014_,
                    v___x_5012_,
                    v___y_4970_,
                    v___y_4971_,
                    v___y_4972_,
                    v___y_4973_,
                    v___y_4974_,
                    v___y_4975_,
                    v___y_4976_,
                    v___y_4977_,
                );
                return v___x_5015_;
            }
            4 => {
                v___x_5022_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5023_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1;
                v_sz_5024_ = lean_array_size(v_val_5018_);
                v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__7(v_val_5018_, v_sz_5024_, v___x_4987_, v___x_5023_);
                v_fst_5026_ = crate::leanh::lean_ctor_get(v___x_5025_, 0);
                v_snd_5027_ = crate::leanh::lean_ctor_get(v___x_5025_, 1);
                v_isSharedCheck_5119_ = (!crate::leanh::lean_is_exclusive(v___x_5025_)) as u8;
                if v_isSharedCheck_5119_ == 0 {
                    v___x_5029_ = v___x_5025_;
                    v_isShared_5030_ = v_isSharedCheck_5119_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_5027_);
                    crate::leanh::lean_inc(v_fst_5026_);
                    crate::leanh::lean_dec(v___x_5025_);
                    v___x_5029_ = crate::leanh::lean_box(0);
                    v_isShared_5030_ = v_isSharedCheck_5119_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_requireClose_4969_ == 0 {
                    v___y_5095_ = v___y_4970_;
                    v___y_5096_ = v___y_4971_;
                    v___y_5097_ = v___y_4972_;
                    v___y_5098_ = v___y_4973_;
                    v___y_5099_ = v___y_4974_;
                    v___y_5100_ = v___y_4975_;
                    v___y_5101_ = v___y_4976_;
                    v___y_5102_ = v___y_4977_;
                    state = 13;
                    continue;
                } else {
                    if v_all_4993_ == 0 {
                        crate::leanh::lean_del_object(v___x_5029_);
                        crate::leanh::lean_dec(v_snd_5027_);
                        crate::leanh::lean_dec(v_fst_5026_);
                        crate::leanh::lean_del_object(v___x_5020_);
                        crate::leanh::lean_dec(v_ref_4968_);
                        crate::leanh::lean_dec_ref(v_a_4967_);
                        crate::leanh::lean_dec(v_a_4966_);
                        crate::leanh::lean_dec(v_snd_4965_);
                        v___x_5115_ = lean_array_get_size(v_val_5018_);
                        crate::leanh::lean_dec(v_val_5018_);
                        v___x_5116_ = lean_nat_dec_eq(v___x_5115_, v___x_5022_);
                        if v___x_5116_ == 0 {
                            v___x_5117_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9;
                            v___y_5110_ = v___x_5117_;
                            state = 14;
                            continue;
                        } else {
                            v___x_5118_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0;
                            v___y_5110_ = v___x_5118_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___y_5095_ = v___y_4970_;
                        v___y_5096_ = v___y_4971_;
                        v___y_5097_ = v___y_4972_;
                        v___y_5098_ = v___y_4973_;
                        v___y_5099_ = v___y_4974_;
                        v___y_5100_ = v___y_4975_;
                        v___y_5101_ = v___y_4976_;
                        v___y_5102_ = v___y_4977_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                if v_requireClose_4969_ == 0 {
                    v___x_5040_ = crate::leanh::lean_box(0);
                    v_sz_5041_ = lean_array_size(v_snd_5027_);
                    v___x_5042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8(v_a_4966_, v_a_4967_, v_ref_4968_, v_snd_5027_, v_sz_5041_, v___x_4987_, v___x_5040_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
                    crate::leanh::lean_dec(v_snd_5027_);
                    if crate::leanh::lean_obj_tag(v___x_5042_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5042_, 1);
                        v___x_5043_ = lean_array_get_size(v_val_5018_);
                        crate::leanh::lean_dec(v_val_5018_);
                        v___x_5044_ = lean_nat_dec_eq(v___x_5043_, v___x_5022_);
                        if v___x_5044_ == 0 {
                            v___y_4980_ = v___y_5036_;
                            v___y_4981_ = v___y_5037_;
                            v___y_4982_ = v___y_5038_;
                            v___y_4983_ = v___y_5039_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5045_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4_once
                                ),
                                _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4,
                            );
                            v___x_5046_ =
                                l_Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9(
                                    v___x_5045_,
                                    v___y_5032_,
                                    v___y_5033_,
                                    v___y_5034_,
                                    v___y_5035_,
                                    v___y_5036_,
                                    v___y_5037_,
                                    v___y_5038_,
                                    v___y_5039_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_5046_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5046_, 1);
                                v___y_4980_ = v___y_5036_;
                                v___y_4981_ = v___y_5037_;
                                v___y_4982_ = v___y_5038_;
                                v___y_4983_ = v___y_5039_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_snd_4965_);
                                return v___x_5046_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_5018_);
                        crate::leanh::lean_dec(v_snd_4965_);
                        return v___x_5042_;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_5027_);
                    crate::leanh::lean_dec(v_val_5018_);
                    crate::leanh::lean_dec(v_ref_4968_);
                    crate::leanh::lean_dec_ref(v_a_4967_);
                    crate::leanh::lean_dec(v_a_4966_);
                    v___y_4980_ = v___y_5036_;
                    v___y_4981_ = v___y_5037_;
                    v___y_4982_ = v___y_5038_;
                    v___y_4983_ = v___y_5039_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_5056_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__6;
                v___x_5057_ = crate::leanh::lean_unsigned_to_nat(90);
                v___x_5058_ = l_Lean_reportOutOfHeartbeats(
                    v___x_5056_,
                    v_ref_4968_,
                    v___x_5057_,
                    v___y_5054_,
                    v___y_5055_,
                );
                if crate::leanh::lean_obj_tag(v___x_5058_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5058_, 1);
                    v_sz_5059_ = lean_array_size(v_fst_5026_);
                    crate::leanh::lean_inc(v_a_4966_);
                    v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10(v_a_4966_, v_sz_5059_, v___x_4987_, v_fst_5026_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
                    if crate::leanh::lean_obj_tag(v___x_5060_) == 0 {
                        v_a_5061_ = crate::leanh::lean_ctor_get(v___x_5060_, 0);
                        crate::leanh::lean_inc(v_a_5061_);
                        crate::leanh::lean_dec_ref_known(v___x_5060_, 1);
                        v___x_5062_ = lean_array_get_size(v_a_5061_);
                        v___x_5063_ = lean_nat_dec_eq(v___x_5062_, v___x_5022_);
                        if v___x_5063_ == 0 {
                            v___x_5064_ = 1;
                            v___x_5065_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc_ref(v_a_4967_);
                            if v_isShared_5021_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_5020_, 0, v_a_4967_);
                                v___x_5067_ = v___x_5020_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_5069_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_4967_);
                                v___x_5067_ = v_reuseFailAlloc_5069_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5061_);
                            crate::leanh::lean_del_object(v___x_5020_);
                            v___y_5032_ = v___y_5048_;
                            v___y_5033_ = v___y_5049_;
                            v___y_5034_ = v___y_5050_;
                            v___y_5035_ = v___y_5051_;
                            v___y_5036_ = v___y_5052_;
                            v___y_5037_ = v___y_5053_;
                            v___y_5038_ = v___y_5054_;
                            v___y_5039_ = v___y_5055_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_5027_);
                        crate::leanh::lean_del_object(v___x_5020_);
                        crate::leanh::lean_dec(v_val_5018_);
                        crate::leanh::lean_dec(v_ref_4968_);
                        crate::leanh::lean_dec_ref(v_a_4967_);
                        crate::leanh::lean_dec(v_a_4966_);
                        crate::leanh::lean_dec(v_snd_4965_);
                        v_a_5070_ = crate::leanh::lean_ctor_get(v___x_5060_, 0);
                        v_isSharedCheck_5077_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5060_)) as u8;
                        if v_isSharedCheck_5077_ == 0 {
                            v___x_5072_ = v___x_5060_;
                            v_isShared_5073_ = v_isSharedCheck_5077_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5070_);
                            crate::leanh::lean_dec(v___x_5060_);
                            v___x_5072_ = crate::leanh::lean_box(0);
                            v_isShared_5073_ = v_isSharedCheck_5077_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_5027_);
                    crate::leanh::lean_dec(v_fst_5026_);
                    crate::leanh::lean_del_object(v___x_5020_);
                    crate::leanh::lean_dec(v_val_5018_);
                    crate::leanh::lean_dec(v_ref_4968_);
                    crate::leanh::lean_dec_ref(v_a_4967_);
                    crate::leanh::lean_dec(v_a_4966_);
                    crate::leanh::lean_dec(v_snd_4965_);
                    return v___x_5058_;
                }
            }
            8 => {
                crate::leanh::lean_inc(v_ref_4968_);
                v___x_5068_ = l_Lean_Meta_Tactic_TryThis_addExactSuggestions(
                    v_ref_4968_,
                    v_a_5061_,
                    v___x_5065_,
                    v___x_5063_,
                    v___x_5065_,
                    v___x_5067_,
                    v___x_5064_,
                    v___y_5048_,
                    v___y_5049_,
                    v___y_5050_,
                    v___y_5051_,
                    v___y_5052_,
                    v___y_5053_,
                    v___y_5054_,
                    v___y_5055_,
                );
                if crate::leanh::lean_obj_tag(v___x_5068_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5068_, 1);
                    v___y_5032_ = v___y_5048_;
                    v___y_5033_ = v___y_5049_;
                    v___y_5034_ = v___y_5050_;
                    v___y_5035_ = v___y_5051_;
                    v___y_5036_ = v___y_5052_;
                    v___y_5037_ = v___y_5053_;
                    v___y_5038_ = v___y_5054_;
                    v___y_5039_ = v___y_5055_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_5027_);
                    crate::leanh::lean_dec(v_val_5018_);
                    crate::leanh::lean_dec(v_ref_4968_);
                    crate::leanh::lean_dec_ref(v_a_4967_);
                    crate::leanh::lean_dec(v_a_4966_);
                    crate::leanh::lean_dec(v_snd_4965_);
                    return v___x_5068_;
                }
            }
            9 => {
                if v_isShared_5073_ == 0 {
                    v___x_5075_ = v___x_5072_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
                    v___x_5075_ = v_reuseFailAlloc_5076_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5075_;
            }
            11 => {
                v___x_5088_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8_once
                    ),
                    _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8,
                );
                crate::leanh::lean_inc_ref(v___y_5087_);
                v___x_5089_ = l_Lean_stringToMessageData(v___y_5087_);
                if v_isShared_5030_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5029_, 7);
                    crate::leanh::lean_ctor_set(v___x_5029_, 1, v___x_5089_);
                    crate::leanh::lean_ctor_set(v___x_5029_, 0, v___x_5088_);
                    v___x_5091_ = v___x_5029_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 0, v___x_5088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 1, v___x_5089_);
                    v___x_5091_ = v_reuseFailAlloc_5093_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5092_ =
                    l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg(
                        v___x_5091_,
                        v___y_5084_,
                        v___y_5082_,
                        v___y_5081_,
                        v___y_5086_,
                    );
                return v___x_5092_;
            }
            13 => {
                if v_requireClose_4969_ == 0 {
                    crate::leanh::lean_del_object(v___x_5029_);
                    v___y_5048_ = v___y_5095_;
                    v___y_5049_ = v___y_5096_;
                    v___y_5050_ = v___y_5097_;
                    v___y_5051_ = v___y_5098_;
                    v___y_5052_ = v___y_5099_;
                    v___y_5053_ = v___y_5100_;
                    v___y_5054_ = v___y_5101_;
                    v___y_5055_ = v___y_5102_;
                    state = 7;
                    continue;
                } else {
                    if v_all_4993_ == 0 {
                        crate::leanh::lean_del_object(v___x_5029_);
                        v___y_5048_ = v___y_5095_;
                        v___y_5049_ = v___y_5096_;
                        v___y_5050_ = v___y_5097_;
                        v___y_5051_ = v___y_5098_;
                        v___y_5052_ = v___y_5099_;
                        v___y_5053_ = v___y_5100_;
                        v___y_5054_ = v___y_5101_;
                        v___y_5055_ = v___y_5102_;
                        state = 7;
                        continue;
                    } else {
                        v___x_5103_ = lean_array_get_size(v_fst_5026_);
                        v___x_5104_ = lean_nat_dec_eq(v___x_5103_, v___x_5022_);
                        if v___x_5104_ == 0 {
                            crate::leanh::lean_del_object(v___x_5029_);
                            v___y_5048_ = v___y_5095_;
                            v___y_5049_ = v___y_5096_;
                            v___y_5050_ = v___y_5097_;
                            v___y_5051_ = v___y_5098_;
                            v___y_5052_ = v___y_5099_;
                            v___y_5053_ = v___y_5100_;
                            v___y_5054_ = v___y_5101_;
                            v___y_5055_ = v___y_5102_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_fst_5026_);
                            crate::leanh::lean_del_object(v___x_5020_);
                            crate::leanh::lean_dec(v_val_5018_);
                            crate::leanh::lean_dec(v_ref_4968_);
                            crate::leanh::lean_dec_ref(v_a_4967_);
                            crate::leanh::lean_dec(v_a_4966_);
                            crate::leanh::lean_dec(v_snd_4965_);
                            v___x_5105_ = lean_array_get_size(v_snd_5027_);
                            crate::leanh::lean_dec(v_snd_5027_);
                            v___x_5106_ = lean_nat_dec_eq(v___x_5105_, v___x_5022_);
                            if v___x_5106_ == 0 {
                                v___x_5107_ =
                                    l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9;
                                v___y_5079_ = v___y_5097_;
                                v___y_5080_ = v___y_5098_;
                                v___y_5081_ = v___y_5101_;
                                v___y_5082_ = v___y_5100_;
                                v___y_5083_ = v___y_5095_;
                                v___y_5084_ = v___y_5099_;
                                v___y_5085_ = v___y_5096_;
                                v___y_5086_ = v___y_5102_;
                                v___y_5087_ = v___x_5107_;
                                state = 11;
                                continue;
                            } else {
                                v___x_5108_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0;
                                v___y_5079_ = v___y_5097_;
                                v___y_5080_ = v___y_5098_;
                                v___y_5081_ = v___y_5101_;
                                v___y_5082_ = v___y_5100_;
                                v___y_5083_ = v___y_5095_;
                                v___y_5084_ = v___y_5099_;
                                v___y_5085_ = v___y_5096_;
                                v___y_5086_ = v___y_5102_;
                                v___y_5087_ = v___x_5108_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                }
            }
            14 => {
                v___x_5111_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8_once
                    ),
                    _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8,
                );
                crate::leanh::lean_inc_ref(v___y_5110_);
                v___x_5112_ = l_Lean_stringToMessageData(v___y_5110_);
                v___x_5113_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5113_, 0, v___x_5111_);
                crate::leanh::lean_ctor_set(v___x_5113_, 1, v___x_5112_);
                v___x_5114_ =
                    l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg(
                        v___x_5113_,
                        v___y_4974_,
                        v___y_4975_,
                        v___y_4976_,
                        v___y_4977_,
                    );
                return v___x_5114_;
            }
            15 => {
                if v_isShared_5124_ == 0 {
                    v___x_5126_ = v___x_5123_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
                    v___x_5126_ = v_reuseFailAlloc_5127_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5126_;
            }
            17 => {
                if v_isShared_5132_ == 0 {
                    v___x_5134_ = v___x_5131_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5135_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5129_);
                    v___x_5134_ = v_reuseFailAlloc_5135_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___boxed(
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v_config_5138_: *mut crate::leanh::LeanObject,
    mut v_snd_5139_: *mut crate::leanh::LeanObject,
    mut v_a_5140_: *mut crate::leanh::LeanObject,
    mut v_a_5141_: *mut crate::leanh::LeanObject,
    mut v_ref_5142_: *mut crate::leanh::LeanObject,
    mut v_requireClose_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v___y_5147_: *mut crate::leanh::LeanObject,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
    mut v___y_5150_: *mut crate::leanh::LeanObject,
    mut v___y_5151_: *mut crate::leanh::LeanObject,
    mut v___y_5152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_requireClose_boxed_5153_: u8 = 0;
    let mut v_res_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_requireClose_boxed_5153_ = (crate::leanh::lean_unbox(v_requireClose_5143_) as u8);
    v_res_5154_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2(
        v___y_5137_,
        v_config_5138_,
        v_snd_5139_,
        v_a_5140_,
        v_a_5141_,
        v_ref_5142_,
        v_requireClose_boxed_5153_,
        v___y_5144_,
        v___y_5145_,
        v___y_5146_,
        v___y_5147_,
        v___y_5148_,
        v___y_5149_,
        v___y_5150_,
        v___y_5151_,
    );
    crate::leanh::lean_dec(v___y_5151_);
    crate::leanh::lean_dec_ref(v___y_5150_);
    crate::leanh::lean_dec(v___y_5149_);
    crate::leanh::lean_dec_ref(v___y_5148_);
    crate::leanh::lean_dec(v___y_5147_);
    crate::leanh::lean_dec_ref(v___y_5146_);
    crate::leanh::lean_dec(v___y_5145_);
    crate::leanh::lean_dec_ref(v___y_5144_);
    crate::leanh::lean_dec_ref(v_config_5138_);
    return v_res_5154_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f(
    mut v_ref_5157_: *mut crate::leanh::LeanObject,
    mut v_config_5158_: *mut crate::leanh::LeanObject,
    mut v_required_5159_: *mut crate::leanh::LeanObject,
    mut v_requireClose_5160_: u8,
    mut v_a_5161_: *mut crate::leanh::LeanObject,
    mut v_a_5162_: *mut crate::leanh::LeanObject,
    mut v_a_5163_: *mut crate::leanh::LeanObject,
    mut v_a_5164_: *mut crate::leanh::LeanObject,
    mut v_a_5165_: *mut crate::leanh::LeanObject,
    mut v_a_5166_: *mut crate::leanh::LeanObject,
    mut v_a_5167_: *mut crate::leanh::LeanObject,
    mut v_a_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5189_: u8 = 0;
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut v_a_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut v_a_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5205_: u8 = 0;
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5209_: u8 = 0;
    let mut v_a_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5213_: u8 = 0;
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5170_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_5162_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_,
                );
                if crate::leanh::lean_obj_tag(v___x_5170_) == 0 {
                    v_a_5171_ = crate::leanh::lean_ctor_get(v___x_5170_, 0);
                    crate::leanh::lean_inc(v_a_5171_);
                    crate::leanh::lean_dec_ref_known(v___x_5170_, 1);
                    v___x_5172_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v_a_5162_, v_a_5164_, v_a_5166_, v_a_5168_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5172_) == 0 {
                        v_a_5173_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                        crate::leanh::lean_inc(v_a_5173_);
                        crate::leanh::lean_dec_ref_known(v___x_5172_, 1);
                        v___x_5174_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                            v_a_5162_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5174_) == 0 {
                            v_a_5175_ = crate::leanh::lean_ctor_get(v___x_5174_, 0);
                            crate::leanh::lean_inc(v_a_5175_);
                            crate::leanh::lean_dec_ref_known(v___x_5174_, 1);
                            v___x_5176_ = l_Lean_MVarId_intros(
                                v_a_5175_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5176_) == 0 {
                                v_a_5177_ = crate::leanh::lean_ctor_get(v___x_5176_, 0);
                                crate::leanh::lean_inc(v_a_5177_);
                                crate::leanh::lean_dec_ref_known(v___x_5176_, 1);
                                v_snd_5178_ = crate::leanh::lean_ctor_get(v_a_5177_, 1);
                                crate::leanh::lean_inc(v_snd_5178_);
                                crate::leanh::lean_dec(v_a_5177_);
                                if crate::leanh::lean_obj_tag(v_required_5159_) == 0 {
                                    v___x_5184_ = l_Lean_Elab_LibrarySearch_exact_x3f___closed__0;
                                    v___y_5180_ = v___x_5184_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_5185_ = crate::leanh::lean_ctor_get(v_required_5159_, 0);
                                    crate::leanh::lean_inc(v_val_5185_);
                                    crate::leanh::lean_dec_ref_known(v_required_5159_, 1);
                                    v___y_5180_ = v_val_5185_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5173_);
                                crate::leanh::lean_dec(v_a_5171_);
                                crate::leanh::lean_dec(v_required_5159_);
                                crate::leanh::lean_dec_ref(v_config_5158_);
                                crate::leanh::lean_dec(v_ref_5157_);
                                v_a_5186_ = crate::leanh::lean_ctor_get(v___x_5176_, 0);
                                v_isSharedCheck_5193_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5176_)) as u8;
                                if v_isSharedCheck_5193_ == 0 {
                                    v___x_5188_ = v___x_5176_;
                                    v_isShared_5189_ = v_isSharedCheck_5193_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5186_);
                                    crate::leanh::lean_dec(v___x_5176_);
                                    v___x_5188_ = crate::leanh::lean_box(0);
                                    v_isShared_5189_ = v_isSharedCheck_5193_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5173_);
                            crate::leanh::lean_dec(v_a_5171_);
                            crate::leanh::lean_dec(v_required_5159_);
                            crate::leanh::lean_dec_ref(v_config_5158_);
                            crate::leanh::lean_dec(v_ref_5157_);
                            v_a_5194_ = crate::leanh::lean_ctor_get(v___x_5174_, 0);
                            v_isSharedCheck_5201_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5174_)) as u8;
                            if v_isSharedCheck_5201_ == 0 {
                                v___x_5196_ = v___x_5174_;
                                v_isShared_5197_ = v_isSharedCheck_5201_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5194_);
                                crate::leanh::lean_dec(v___x_5174_);
                                v___x_5196_ = crate::leanh::lean_box(0);
                                v_isShared_5197_ = v_isSharedCheck_5201_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5171_);
                        crate::leanh::lean_dec(v_required_5159_);
                        crate::leanh::lean_dec_ref(v_config_5158_);
                        crate::leanh::lean_dec(v_ref_5157_);
                        v_a_5202_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                        v_isSharedCheck_5209_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5172_)) as u8;
                        if v_isSharedCheck_5209_ == 0 {
                            v___x_5204_ = v___x_5172_;
                            v_isShared_5205_ = v_isSharedCheck_5209_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5202_);
                            crate::leanh::lean_dec(v___x_5172_);
                            v___x_5204_ = crate::leanh::lean_box(0);
                            v_isShared_5205_ = v_isSharedCheck_5209_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_required_5159_);
                    crate::leanh::lean_dec_ref(v_config_5158_);
                    crate::leanh::lean_dec(v_ref_5157_);
                    v_a_5210_ = crate::leanh::lean_ctor_get(v___x_5170_, 0);
                    v_isSharedCheck_5217_ = (!crate::leanh::lean_is_exclusive(v___x_5170_)) as u8;
                    if v_isSharedCheck_5217_ == 0 {
                        v___x_5212_ = v___x_5170_;
                        v_isShared_5213_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5210_);
                        crate::leanh::lean_dec(v___x_5170_);
                        v___x_5212_ = crate::leanh::lean_box(0);
                        v_isShared_5213_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5181_ = crate::leanh::lean_box((v_requireClose_5160_) as usize);
                crate::leanh::lean_inc(v_snd_5178_);
                v___f_5182_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___boxed as *mut core::ffi::c_void,
                    16,
                    7,
                );
                crate::leanh::lean_closure_set(v___f_5182_, 0, v___y_5180_);
                crate::leanh::lean_closure_set(v___f_5182_, 1, v_config_5158_);
                crate::leanh::lean_closure_set(v___f_5182_, 2, v_snd_5178_);
                crate::leanh::lean_closure_set(v___f_5182_, 3, v_a_5171_);
                crate::leanh::lean_closure_set(v___f_5182_, 4, v_a_5173_);
                crate::leanh::lean_closure_set(v___f_5182_, 5, v_ref_5157_);
                crate::leanh::lean_closure_set(v___f_5182_, 6, v___x_5181_);
                v___x_5183_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___redArg(v_snd_5178_, v___f_5182_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
                return v___x_5183_;
            }
            2 => {
                if v_isShared_5189_ == 0 {
                    v___x_5191_ = v___x_5188_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
                    v___x_5191_ = v_reuseFailAlloc_5192_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5191_;
            }
            4 => {
                if v_isShared_5197_ == 0 {
                    v___x_5199_ = v___x_5196_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5200_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
                    v___x_5199_ = v_reuseFailAlloc_5200_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5199_;
            }
            6 => {
                if v_isShared_5205_ == 0 {
                    v___x_5207_ = v___x_5204_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
                    v___x_5207_ = v_reuseFailAlloc_5208_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5207_;
            }
            8 => {
                if v_isShared_5213_ == 0 {
                    v___x_5215_ = v___x_5212_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
                    v___x_5215_ = v_reuseFailAlloc_5216_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___boxed(
    mut v_ref_5218_: *mut crate::leanh::LeanObject,
    mut v_config_5219_: *mut crate::leanh::LeanObject,
    mut v_required_5220_: *mut crate::leanh::LeanObject,
    mut v_requireClose_5221_: *mut crate::leanh::LeanObject,
    mut v_a_5222_: *mut crate::leanh::LeanObject,
    mut v_a_5223_: *mut crate::leanh::LeanObject,
    mut v_a_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_a_5226_: *mut crate::leanh::LeanObject,
    mut v_a_5227_: *mut crate::leanh::LeanObject,
    mut v_a_5228_: *mut crate::leanh::LeanObject,
    mut v_a_5229_: *mut crate::leanh::LeanObject,
    mut v_a_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_requireClose_boxed_5231_: u8 = 0;
    let mut v_res_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_requireClose_boxed_5231_ = (crate::leanh::lean_unbox(v_requireClose_5221_) as u8);
    v_res_5232_ = l_Lean_Elab_LibrarySearch_exact_x3f(
        v_ref_5218_,
        v_config_5219_,
        v_required_5220_,
        v_requireClose_boxed_5231_,
        v_a_5222_,
        v_a_5223_,
        v_a_5224_,
        v_a_5225_,
        v_a_5226_,
        v_a_5227_,
        v_a_5228_,
        v_a_5229_,
    );
    crate::leanh::lean_dec(v_a_5229_);
    crate::leanh::lean_dec_ref(v_a_5228_);
    crate::leanh::lean_dec(v_a_5227_);
    crate::leanh::lean_dec_ref(v_a_5226_);
    crate::leanh::lean_dec(v_a_5225_);
    crate::leanh::lean_dec_ref(v_a_5224_);
    crate::leanh::lean_dec(v_a_5223_);
    crate::leanh::lean_dec_ref(v_a_5222_);
    return v_res_5232_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11(
    mut v_00_u03b1_5233_: *mut crate::leanh::LeanObject,
    mut v_msg_5234_: *mut crate::leanh::LeanObject,
    mut v___y_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
    mut v___y_5237_: *mut crate::leanh::LeanObject,
    mut v___y_5238_: *mut crate::leanh::LeanObject,
    mut v___y_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
    mut v___y_5242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5244_ = l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg(
        v_msg_5234_,
        v___y_5239_,
        v___y_5240_,
        v___y_5241_,
        v___y_5242_,
    );
    return v___x_5244_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___boxed(
    mut v_00_u03b1_5245_: *mut crate::leanh::LeanObject,
    mut v_msg_5246_: *mut crate::leanh::LeanObject,
    mut v___y_5247_: *mut crate::leanh::LeanObject,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
    mut v___y_5249_: *mut crate::leanh::LeanObject,
    mut v___y_5250_: *mut crate::leanh::LeanObject,
    mut v___y_5251_: *mut crate::leanh::LeanObject,
    mut v___y_5252_: *mut crate::leanh::LeanObject,
    mut v___y_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5256_ = l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11(
        v_00_u03b1_5245_,
        v_msg_5246_,
        v___y_5247_,
        v___y_5248_,
        v___y_5249_,
        v___y_5250_,
        v___y_5251_,
        v___y_5252_,
        v___y_5253_,
        v___y_5254_,
    );
    crate::leanh::lean_dec(v___y_5254_);
    crate::leanh::lean_dec_ref(v___y_5253_);
    crate::leanh::lean_dec(v___y_5252_);
    crate::leanh::lean_dec_ref(v___y_5251_);
    crate::leanh::lean_dec(v___y_5250_);
    crate::leanh::lean_dec_ref(v___y_5249_);
    crate::leanh::lean_dec(v___y_5248_);
    crate::leanh::lean_dec_ref(v___y_5247_);
    return v_res_5256_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11(
    mut v_ref_5257_: *mut crate::leanh::LeanObject,
    mut v_msgData_5258_: *mut crate::leanh::LeanObject,
    mut v_severity_5259_: u8,
    mut v_isSilent_5260_: u8,
    mut v___y_5261_: *mut crate::leanh::LeanObject,
    mut v___y_5262_: *mut crate::leanh::LeanObject,
    mut v___y_5263_: *mut crate::leanh::LeanObject,
    mut v___y_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5270_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(v_ref_5257_, v_msgData_5258_, v_severity_5259_, v_isSilent_5260_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
    return v___x_5270_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___boxed(
    mut v_ref_5271_: *mut crate::leanh::LeanObject,
    mut v_msgData_5272_: *mut crate::leanh::LeanObject,
    mut v_severity_5273_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5274_: *mut crate::leanh::LeanObject,
    mut v___y_5275_: *mut crate::leanh::LeanObject,
    mut v___y_5276_: *mut crate::leanh::LeanObject,
    mut v___y_5277_: *mut crate::leanh::LeanObject,
    mut v___y_5278_: *mut crate::leanh::LeanObject,
    mut v___y_5279_: *mut crate::leanh::LeanObject,
    mut v___y_5280_: *mut crate::leanh::LeanObject,
    mut v___y_5281_: *mut crate::leanh::LeanObject,
    mut v___y_5282_: *mut crate::leanh::LeanObject,
    mut v___y_5283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5284_: u8 = 0;
    let mut v_isSilent_boxed_5285_: u8 = 0;
    let mut v_res_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5284_ = (crate::leanh::lean_unbox(v_severity_5273_) as u8);
    v_isSilent_boxed_5285_ = (crate::leanh::lean_unbox(v_isSilent_5274_) as u8);
    v_res_5286_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11(v_ref_5271_, v_msgData_5272_, v_severity_boxed_5284_, v_isSilent_boxed_5285_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
    crate::leanh::lean_dec(v___y_5282_);
    crate::leanh::lean_dec_ref(v___y_5281_);
    crate::leanh::lean_dec(v___y_5280_);
    crate::leanh::lean_dec_ref(v___y_5279_);
    crate::leanh::lean_dec(v___y_5278_);
    crate::leanh::lean_dec_ref(v___y_5277_);
    crate::leanh::lean_dec(v___y_5276_);
    crate::leanh::lean_dec_ref(v___y_5275_);
    crate::leanh::lean_dec(v_ref_5271_);
    return v_res_5286_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5287_ = crate::leanh::lean_box(0);
    v___x_5288_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_5289_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5289_, 0, v___x_5288_);
    crate::leanh::lean_ctor_set(v___x_5289_, 1, v___x_5287_);
    return v___x_5289_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5291_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0);
    v___x_5292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5292_, 0, v___x_5291_);
    return v___x_5292_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___boxed(
    mut v___y_5293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
    return v_res_5294_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0(
    mut v_00_u03b1_5295_: *mut crate::leanh::LeanObject,
    mut v___y_5296_: *mut crate::leanh::LeanObject,
    mut v___y_5297_: *mut crate::leanh::LeanObject,
    mut v___y_5298_: *mut crate::leanh::LeanObject,
    mut v___y_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
    mut v___y_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5305_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
    return v___x_5305_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___boxed(
    mut v_00_u03b1_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
    mut v___y_5308_: *mut crate::leanh::LeanObject,
    mut v___y_5309_: *mut crate::leanh::LeanObject,
    mut v___y_5310_: *mut crate::leanh::LeanObject,
    mut v___y_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5316_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0(
            v_00_u03b1_5306_,
            v___y_5307_,
            v___y_5308_,
            v___y_5309_,
            v___y_5310_,
            v___y_5311_,
            v___y_5312_,
            v___y_5313_,
            v___y_5314_,
        );
    crate::leanh::lean_dec(v___y_5314_);
    crate::leanh::lean_dec_ref(v___y_5313_);
    crate::leanh::lean_dec(v___y_5312_);
    crate::leanh::lean_dec_ref(v___y_5311_);
    crate::leanh::lean_dec(v___y_5310_);
    crate::leanh::lean_dec_ref(v___y_5309_);
    crate::leanh::lean_dec(v___y_5308_);
    crate::leanh::lean_dec_ref(v___y_5307_);
    return v_res_5316_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__1(
    mut v_sz_5317_: usize,
    mut v_i_5318_: usize,
    mut v_bs_5319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5320_: u8 = 0;
    let mut v_v_5321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: usize = 0;
    let mut v___x_5325_: usize = 0;
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5320_ = lean_usize_dec_lt(v_i_5318_, v_sz_5317_);
                if v___x_5320_ == 0 {
                    return v_bs_5319_;
                } else {
                    v_v_5321_ = lean_array_uget(v_bs_5319_, v_i_5318_);
                    v___x_5322_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5323_ = lean_array_uset(v_bs_5319_, v_i_5318_, v___x_5322_);
                    v___x_5324_ = 1usize;
                    v___x_5325_ = lean_usize_add(v_i_5318_, v___x_5324_);
                    v___x_5326_ = lean_array_uset(v_bs_x27_5323_, v_i_5318_, v_v_5321_);
                    v_i_5318_ = v___x_5325_;
                    v_bs_5319_ = v___x_5326_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__1___boxed(
    mut v_sz_5328_: *mut crate::leanh::LeanObject,
    mut v_i_5329_: *mut crate::leanh::LeanObject,
    mut v_bs_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5331_: usize = 0;
    let mut v_i_boxed_5332_: usize = 0;
    let mut v_res_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5331_ = crate::leanh::lean_unbox_usize(v_sz_5328_);
    crate::leanh::lean_dec(v_sz_5328_);
    v_i_boxed_5332_ = crate::leanh::lean_unbox_usize(v_i_5329_);
    crate::leanh::lean_dec(v_i_5329_);
    v_res_5333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__1(v_sz_boxed_5331_, v_i_boxed_5332_, v_bs_5330_);
    return v_res_5333_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__2(
    mut v_sz_5334_: usize,
    mut v_i_5335_: usize,
    mut v_bs_5336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: usize = 0;
    let mut v___x_5343_: usize = 0;
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5337_ = lean_usize_dec_lt(v_i_5335_, v_sz_5334_);
                if v___x_5337_ == 0 {
                    v___x_5338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5338_, 0, v_bs_5336_);
                    return v___x_5338_;
                } else {
                    v_v_5339_ = lean_array_uget(v_bs_5336_, v_i_5335_);
                    v___x_5340_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5341_ = lean_array_uset(v_bs_5336_, v_i_5335_, v___x_5340_);
                    v___x_5342_ = 1usize;
                    v___x_5343_ = lean_usize_add(v_i_5335_, v___x_5342_);
                    v___x_5344_ = lean_array_uset(v_bs_x27_5341_, v_i_5335_, v_v_5339_);
                    v_i_5335_ = v___x_5343_;
                    v_bs_5336_ = v___x_5344_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__2___boxed(
    mut v_sz_5346_: *mut crate::leanh::LeanObject,
    mut v_i_5347_: *mut crate::leanh::LeanObject,
    mut v_bs_5348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5349_: usize = 0;
    let mut v_i_boxed_5350_: usize = 0;
    let mut v_res_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5349_ = crate::leanh::lean_unbox_usize(v_sz_5346_);
    crate::leanh::lean_dec(v_sz_5346_);
    v_i_boxed_5350_ = crate::leanh::lean_unbox_usize(v_i_5347_);
    crate::leanh::lean_dec(v_i_5347_);
    v_res_5351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__2(v_sz_boxed_5349_, v_i_boxed_5350_, v_bs_5348_);
    return v_res_5351_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(
    mut v___x_5352_: u8,
    mut v___x_5353_: u8,
    mut v_as_5354_: *mut crate::leanh::LeanObject,
    mut v_i_5355_: usize,
    mut v_stop_5356_: usize,
    mut v_b_5357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5363_: u8 = 0;
    let mut v_fst_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: u8 = 0;
    let mut v_snd_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_unused_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5379_: u8 = 0;
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut v_unused_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5363_ = lean_usize_dec_eq(v_i_5355_, v_stop_5356_);
                if v___x_5363_ == 0 {
                    v_fst_5364_ = crate::leanh::lean_ctor_get(v_b_5357_, 0);
                    v___x_5365_ = (crate::leanh::lean_unbox(v_fst_5364_) as u8);
                    if v___x_5365_ == 0 {
                        v_snd_5366_ = crate::leanh::lean_ctor_get(v_b_5357_, 1);
                        v_isSharedCheck_5374_ = (!crate::leanh::lean_is_exclusive(v_b_5357_)) as u8;
                        if v_isSharedCheck_5374_ == 0 {
                            v_unused_5375_ = crate::leanh::lean_ctor_get(v_b_5357_, 0);
                            crate::leanh::lean_dec(v_unused_5375_);
                            v___x_5368_ = v_b_5357_;
                            v_isShared_5369_ = v_isSharedCheck_5374_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_5366_);
                            crate::leanh::lean_dec(v_b_5357_);
                            v___x_5368_ = crate::leanh::lean_box(0);
                            v_isShared_5369_ = v_isSharedCheck_5374_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_5376_ = crate::leanh::lean_ctor_get(v_b_5357_, 1);
                        v_isSharedCheck_5386_ = (!crate::leanh::lean_is_exclusive(v_b_5357_)) as u8;
                        if v_isSharedCheck_5386_ == 0 {
                            v_unused_5387_ = crate::leanh::lean_ctor_get(v_b_5357_, 0);
                            crate::leanh::lean_dec(v_unused_5387_);
                            v___x_5378_ = v_b_5357_;
                            v_isShared_5379_ = v_isSharedCheck_5386_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_5376_);
                            crate::leanh::lean_dec(v_b_5357_);
                            v___x_5378_ = crate::leanh::lean_box(0);
                            v_isShared_5379_ = v_isSharedCheck_5386_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_5357_;
                }
            }
            1 => {
                v___x_5360_ = 1usize;
                v___x_5361_ = lean_usize_add(v_i_5355_, v___x_5360_);
                v_i_5355_ = v___x_5361_;
                v_b_5357_ = v___y_5359_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5370_ = crate::leanh::lean_box((v___x_5352_) as usize);
                if v_isShared_5369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5368_, 0, v___x_5370_);
                    v___x_5372_ = v___x_5368_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5373_, 1, v_snd_5366_);
                    v___x_5372_ = v_reuseFailAlloc_5373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_5359_ = v___x_5372_;
                state = 1;
                continue;
            }
            4 => {
                v___x_5380_ = lean_array_uget_borrowed(v_as_5354_, v_i_5355_);
                crate::leanh::lean_inc(v___x_5380_);
                v___x_5381_ = lean_array_push(v_snd_5376_, v___x_5380_);
                v___x_5382_ = crate::leanh::lean_box((v___x_5353_) as usize);
                if v_isShared_5379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5378_, 1, v___x_5381_);
                    crate::leanh::lean_ctor_set(v___x_5378_, 0, v___x_5382_);
                    v___x_5384_ = v___x_5378_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5385_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 0, v___x_5382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5385_, 1, v___x_5381_);
                    v___x_5384_ = v_reuseFailAlloc_5385_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_5359_ = v___x_5384_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3___boxed(
    mut v___x_5388_: *mut crate::leanh::LeanObject,
    mut v___x_5389_: *mut crate::leanh::LeanObject,
    mut v_as_5390_: *mut crate::leanh::LeanObject,
    mut v_i_5391_: *mut crate::leanh::LeanObject,
    mut v_stop_5392_: *mut crate::leanh::LeanObject,
    mut v_b_5393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2777__boxed_5394_: u8 = 0;
    let mut v___x_2778__boxed_5395_: u8 = 0;
    let mut v_i_boxed_5396_: usize = 0;
    let mut v_stop_boxed_5397_: usize = 0;
    let mut v_res_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2777__boxed_5394_ = (crate::leanh::lean_unbox(v___x_5388_) as u8);
    v___x_2778__boxed_5395_ = (crate::leanh::lean_unbox(v___x_5389_) as u8);
    v_i_boxed_5396_ = crate::leanh::lean_unbox_usize(v_i_5391_);
    crate::leanh::lean_dec(v_i_5391_);
    v_stop_boxed_5397_ = crate::leanh::lean_unbox_usize(v_stop_5392_);
    crate::leanh::lean_dec(v_stop_5392_);
    v_res_5398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_2777__boxed_5394_, v___x_2778__boxed_5395_, v_as_5390_, v_i_boxed_5396_, v_stop_boxed_5397_, v_b_5393_);
    crate::leanh::lean_dec_ref(v_as_5390_);
    return v_res_5398_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_evalExact(
    mut v_stx_5413_: *mut crate::leanh::LeanObject,
    mut v_a_5414_: *mut crate::leanh::LeanObject,
    mut v_a_5415_: *mut crate::leanh::LeanObject,
    mut v_a_5416_: *mut crate::leanh::LeanObject,
    mut v_a_5417_: *mut crate::leanh::LeanObject,
    mut v_a_5418_: *mut crate::leanh::LeanObject,
    mut v_a_5419_: *mut crate::leanh::LeanObject,
    mut v_a_5420_: *mut crate::leanh::LeanObject,
    mut v_a_5421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: u8 = 0;
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: u8 = 0;
    let mut v_required_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: u8 = 0;
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v_sz_5452_: usize = 0;
    let mut v___x_5453_: usize = 0;
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v_a_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v___y_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5470_: usize = 0;
    let mut v___x_5471_: usize = 0;
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: u8 = 0;
    let mut v___x_5478_: u8 = 0;
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: u8 = 0;
    let mut v___x_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: u8 = 0;
    let mut v___x_5489_: usize = 0;
    let mut v___x_5490_: usize = 0;
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: usize = 0;
    let mut v___x_5494_: usize = 0;
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5423_ = l_Lean_Elab_LibrarySearch_evalExact___closed__1;
                crate::leanh::lean_inc(v_stx_5413_);
                v___x_5424_ = l_Lean_Syntax_isOfKind(v_stx_5413_, v___x_5423_);
                if v___x_5424_ == 0 {
                    crate::leanh::lean_dec(v_stx_5413_);
                    v___x_5425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                    return v___x_5425_;
                } else {
                    v___x_5426_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5427_ = l_Lean_Syntax_getArg(v_stx_5413_, v___x_5426_);
                    v___x_5428_ = l_Lean_Elab_LibrarySearch_evalExact___closed__3;
                    crate::leanh::lean_inc(v___x_5427_);
                    v___x_5429_ = l_Lean_Syntax_isOfKind(v___x_5427_, v___x_5428_);
                    if v___x_5429_ == 0 {
                        crate::leanh::lean_dec(v___x_5427_);
                        crate::leanh::lean_dec(v_stx_5413_);
                        v___x_5474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                        return v___x_5474_;
                    } else {
                        v___x_5475_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_5476_ = l_Lean_Syntax_getArg(v_stx_5413_, v___x_5475_);
                        crate::leanh::lean_dec(v_stx_5413_);
                        v___x_5477_ = l_Lean_Syntax_isNone(v___x_5476_);
                        if v___x_5477_ == 0 {
                            crate::leanh::lean_inc(v___x_5476_);
                            v___x_5478_ = l_Lean_Syntax_matchesNull(v___x_5476_, v___x_5475_);
                            if v___x_5478_ == 0 {
                                crate::leanh::lean_dec(v___x_5476_);
                                crate::leanh::lean_dec(v___x_5427_);
                                v___x_5479_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                                return v___x_5479_;
                            } else {
                                v___x_5480_ = l_Lean_Syntax_getArg(v___x_5476_, v___x_5426_);
                                crate::leanh::lean_dec(v___x_5476_);
                                v___x_5481_ = l_Lean_Syntax_getArgs(v___x_5480_);
                                crate::leanh::lean_dec(v___x_5480_);
                                v___x_5482_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_5483_ = l_Lean_Elab_LibrarySearch_evalExact___closed__4;
                                v___x_5484_ = lean_array_get_size(v___x_5481_);
                                v___x_5485_ = lean_nat_dec_lt(v___x_5482_, v___x_5484_);
                                if v___x_5485_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_5481_);
                                    v___y_5469_ = v___x_5483_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_5486_ = crate::leanh::lean_box((v___x_5429_) as usize);
                                    v___x_5487_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_5487_, 0, v___x_5486_);
                                    crate::leanh::lean_ctor_set(v___x_5487_, 1, v___x_5483_);
                                    v___x_5488_ = lean_nat_dec_le(v___x_5484_, v___x_5484_);
                                    if v___x_5488_ == 0 {
                                        if v___x_5485_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5487_, 2);
                                            crate::leanh::lean_dec_ref(v___x_5481_);
                                            v___y_5469_ = v___x_5483_;
                                            state = 6;
                                            continue;
                                        } else {
                                            v___x_5489_ = 0usize;
                                            v___x_5490_ = lean_usize_of_nat(v___x_5484_);
                                            v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5429_, v___x_5477_, v___x_5481_, v___x_5489_, v___x_5490_, v___x_5487_);
                                            crate::leanh::lean_dec_ref(v___x_5481_);
                                            v_snd_5492_ =
                                                crate::leanh::lean_ctor_get(v___x_5491_, 1);
                                            crate::leanh::lean_inc(v_snd_5492_);
                                            crate::leanh::lean_dec_ref(v___x_5491_);
                                            v___y_5469_ = v_snd_5492_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        v___x_5493_ = 0usize;
                                        v___x_5494_ = lean_usize_of_nat(v___x_5484_);
                                        v___x_5495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5429_, v___x_5477_, v___x_5481_, v___x_5493_, v___x_5494_, v___x_5487_);
                                        crate::leanh::lean_dec_ref(v___x_5481_);
                                        v_snd_5496_ = crate::leanh::lean_ctor_get(v___x_5495_, 1);
                                        crate::leanh::lean_inc(v_snd_5496_);
                                        crate::leanh::lean_dec_ref(v___x_5495_);
                                        v___y_5469_ = v_snd_5496_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_5476_);
                            v___x_5497_ = crate::leanh::lean_box(0);
                            v_required_5431_ = v___x_5497_;
                            v___y_5432_ = v_a_5414_;
                            v___y_5433_ = v_a_5415_;
                            v___y_5434_ = v_a_5416_;
                            v___y_5435_ = v_a_5417_;
                            v___y_5436_ = v_a_5418_;
                            v___y_5437_ = v_a_5419_;
                            v___y_5438_ = v_a_5420_;
                            v___y_5439_ = v_a_5421_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5440_ = 0;
                v___x_5441_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_5441_, 0 as u32, v___x_5440_);
                crate::leanh::lean_ctor_set_uint8(v___x_5441_, 1 as u32, v___x_5440_);
                crate::leanh::lean_ctor_set_uint8(v___x_5441_, 2 as u32, v___x_5429_);
                crate::leanh::lean_ctor_set_uint8(v___x_5441_, 3 as u32, v___x_5440_);
                v___x_5442_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
                    v___x_5427_,
                    v___x_5441_,
                    v___x_5429_,
                    v___y_5432_,
                    v___y_5438_,
                    v___y_5439_,
                );
                if crate::leanh::lean_obj_tag(v___x_5442_) == 0 {
                    if crate::leanh::lean_obj_tag(v_required_5431_) == 0 {
                        v_a_5443_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                        crate::leanh::lean_inc(v_a_5443_);
                        crate::leanh::lean_dec_ref_known(v___x_5442_, 1);
                        v_ref_5444_ = crate::leanh::lean_ctor_get(v___y_5438_, 5);
                        crate::leanh::lean_inc(v_ref_5444_);
                        v___x_5445_ = l_Lean_Elab_LibrarySearch_exact_x3f(
                            v_ref_5444_,
                            v_a_5443_,
                            v_required_5431_,
                            v___x_5429_,
                            v___y_5432_,
                            v___y_5433_,
                            v___y_5434_,
                            v___y_5435_,
                            v___y_5436_,
                            v___y_5437_,
                            v___y_5438_,
                            v___y_5439_,
                        );
                        return v___x_5445_;
                    } else {
                        v_a_5446_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                        crate::leanh::lean_inc(v_a_5446_);
                        crate::leanh::lean_dec_ref_known(v___x_5442_, 1);
                        v_ref_5447_ = crate::leanh::lean_ctor_get(v___y_5438_, 5);
                        v_val_5448_ = crate::leanh::lean_ctor_get(v_required_5431_, 0);
                        v_isSharedCheck_5459_ =
                            (!crate::leanh::lean_is_exclusive(v_required_5431_)) as u8;
                        if v_isSharedCheck_5459_ == 0 {
                            v___x_5450_ = v_required_5431_;
                            v_isShared_5451_ = v_isSharedCheck_5459_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5448_);
                            crate::leanh::lean_dec(v_required_5431_);
                            v___x_5450_ = crate::leanh::lean_box(0);
                            v_isShared_5451_ = v_isSharedCheck_5459_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_required_5431_);
                    v_a_5460_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                    v_isSharedCheck_5467_ = (!crate::leanh::lean_is_exclusive(v___x_5442_)) as u8;
                    if v_isSharedCheck_5467_ == 0 {
                        v___x_5462_ = v___x_5442_;
                        v_isShared_5463_ = v_isSharedCheck_5467_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5460_);
                        crate::leanh::lean_dec(v___x_5442_);
                        v___x_5462_ = crate::leanh::lean_box(0);
                        v_isShared_5463_ = v_isSharedCheck_5467_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_sz_5452_ = lean_array_size(v_val_5448_);
                v___x_5453_ = 0usize;
                v___x_5454_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__1(v_sz_5452_, v___x_5453_, v_val_5448_);
                if v_isShared_5451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5450_, 0, v___x_5454_);
                    v___x_5456_ = v___x_5450_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5454_);
                    v___x_5456_ = v_reuseFailAlloc_5458_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v_ref_5447_);
                v___x_5457_ = l_Lean_Elab_LibrarySearch_exact_x3f(
                    v_ref_5447_,
                    v_a_5446_,
                    v___x_5456_,
                    v___x_5429_,
                    v___y_5432_,
                    v___y_5433_,
                    v___y_5434_,
                    v___y_5435_,
                    v___y_5436_,
                    v___y_5437_,
                    v___y_5438_,
                    v___y_5439_,
                );
                return v___x_5457_;
            }
            4 => {
                if v_isShared_5463_ == 0 {
                    v___x_5465_ = v___x_5462_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5465_;
            }
            6 => {
                v_sz_5470_ = lean_array_size(v___y_5469_);
                v___x_5471_ = 0usize;
                v___x_5472_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__2(v_sz_5470_, v___x_5471_, v___y_5469_);
                if crate::leanh::lean_obj_tag(v___x_5472_) == 0 {
                    crate::leanh::lean_dec(v___x_5427_);
                    v___x_5473_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                    return v___x_5473_;
                } else {
                    v_required_5431_ = v___x_5472_;
                    v___y_5432_ = v_a_5414_;
                    v___y_5433_ = v_a_5415_;
                    v___y_5434_ = v_a_5416_;
                    v___y_5435_ = v_a_5417_;
                    v___y_5436_ = v_a_5418_;
                    v___y_5437_ = v_a_5419_;
                    v___y_5438_ = v_a_5420_;
                    v___y_5439_ = v_a_5421_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_evalExact___boxed(
    mut v_stx_5498_: *mut crate::leanh::LeanObject,
    mut v_a_5499_: *mut crate::leanh::LeanObject,
    mut v_a_5500_: *mut crate::leanh::LeanObject,
    mut v_a_5501_: *mut crate::leanh::LeanObject,
    mut v_a_5502_: *mut crate::leanh::LeanObject,
    mut v_a_5503_: *mut crate::leanh::LeanObject,
    mut v_a_5504_: *mut crate::leanh::LeanObject,
    mut v_a_5505_: *mut crate::leanh::LeanObject,
    mut v_a_5506_: *mut crate::leanh::LeanObject,
    mut v_a_5507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5508_ = l_Lean_Elab_LibrarySearch_evalExact(
        v_stx_5498_,
        v_a_5499_,
        v_a_5500_,
        v_a_5501_,
        v_a_5502_,
        v_a_5503_,
        v_a_5504_,
        v_a_5505_,
        v_a_5506_,
    );
    crate::leanh::lean_dec(v_a_5506_);
    crate::leanh::lean_dec_ref(v_a_5505_);
    crate::leanh::lean_dec(v_a_5504_);
    crate::leanh::lean_dec_ref(v_a_5503_);
    crate::leanh::lean_dec(v_a_5502_);
    crate::leanh::lean_dec_ref(v_a_5501_);
    crate::leanh::lean_dec(v_a_5500_);
    crate::leanh::lean_dec_ref(v_a_5499_);
    return v_res_5508_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5517_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5518_ = l_Lean_Elab_LibrarySearch_evalExact___closed__1;
    v___x_5519_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2;
    v___x_5520_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_LibrarySearch_evalExact___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5521_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5517_,
        v___x_5518_,
        v___x_5519_,
        v___x_5520_,
    );
    return v___x_5521_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___boxed(
    mut v_a_5522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5523_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1();
    return v_res_5523_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5550_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2;
    v___x_5551_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6;
    v___x_5552_ = l_Lean_addBuiltinDeclarationRanges(v___x_5550_, v___x_5551_);
    return v___x_5552_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___boxed(
    mut v_a_5553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5554_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3();
    return v_res_5554_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalApply_spec__0(
    mut v_sz_5555_: usize,
    mut v_i_5556_: usize,
    mut v_bs_5557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: usize = 0;
    let mut v___x_5564_: usize = 0;
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5558_ = lean_usize_dec_lt(v_i_5556_, v_sz_5555_);
                if v___x_5558_ == 0 {
                    v___x_5559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5559_, 0, v_bs_5557_);
                    return v___x_5559_;
                } else {
                    v_v_5560_ = lean_array_uget(v_bs_5557_, v_i_5556_);
                    v___x_5561_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5562_ = lean_array_uset(v_bs_5557_, v_i_5556_, v___x_5561_);
                    v___x_5563_ = 1usize;
                    v___x_5564_ = lean_usize_add(v_i_5556_, v___x_5563_);
                    v___x_5565_ = lean_array_uset(v_bs_x27_5562_, v_i_5556_, v_v_5560_);
                    v_i_5556_ = v___x_5564_;
                    v_bs_5557_ = v___x_5565_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalApply_spec__0___boxed(
    mut v_sz_5567_: *mut crate::leanh::LeanObject,
    mut v_i_5568_: *mut crate::leanh::LeanObject,
    mut v_bs_5569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5570_: usize = 0;
    let mut v_i_boxed_5571_: usize = 0;
    let mut v_res_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5570_ = crate::leanh::lean_unbox_usize(v_sz_5567_);
    crate::leanh::lean_dec(v_sz_5567_);
    v_i_boxed_5571_ = crate::leanh::lean_unbox_usize(v_i_5568_);
    crate::leanh::lean_dec(v_i_5568_);
    v_res_5572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalApply_spec__0(v_sz_boxed_5570_, v_i_boxed_5571_, v_bs_5569_);
    return v_res_5572_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_evalApply(
    mut v_stx_5578_: *mut crate::leanh::LeanObject,
    mut v_a_5579_: *mut crate::leanh::LeanObject,
    mut v_a_5580_: *mut crate::leanh::LeanObject,
    mut v_a_5581_: *mut crate::leanh::LeanObject,
    mut v_a_5582_: *mut crate::leanh::LeanObject,
    mut v_a_5583_: *mut crate::leanh::LeanObject,
    mut v_a_5584_: *mut crate::leanh::LeanObject,
    mut v_a_5585_: *mut crate::leanh::LeanObject,
    mut v_a_5586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: u8 = 0;
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v_required_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: u8 = 0;
    let mut v___x_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5618_: u8 = 0;
    let mut v___y_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5621_: usize = 0;
    let mut v___x_5622_: usize = 0;
    let mut v___x_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: u8 = 0;
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: u8 = 0;
    let mut v___x_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: u8 = 0;
    let mut v___x_5640_: usize = 0;
    let mut v___x_5641_: usize = 0;
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: usize = 0;
    let mut v___x_5645_: usize = 0;
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5588_ = l_Lean_Elab_LibrarySearch_evalApply___closed__0;
                crate::leanh::lean_inc(v_stx_5578_);
                v___x_5589_ = l_Lean_Syntax_isOfKind(v_stx_5578_, v___x_5588_);
                if v___x_5589_ == 0 {
                    crate::leanh::lean_dec(v_stx_5578_);
                    v___x_5590_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                    return v___x_5590_;
                } else {
                    v___x_5591_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5592_ = l_Lean_Syntax_getArg(v_stx_5578_, v___x_5591_);
                    v___x_5593_ = l_Lean_Elab_LibrarySearch_evalExact___closed__3;
                    crate::leanh::lean_inc(v___x_5592_);
                    v___x_5594_ = l_Lean_Syntax_isOfKind(v___x_5592_, v___x_5593_);
                    if v___x_5594_ == 0 {
                        crate::leanh::lean_dec(v___x_5592_);
                        crate::leanh::lean_dec(v_stx_5578_);
                        v___x_5625_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                        return v___x_5625_;
                    } else {
                        v___x_5626_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_5627_ = l_Lean_Syntax_getArg(v_stx_5578_, v___x_5626_);
                        crate::leanh::lean_dec(v_stx_5578_);
                        v___x_5628_ = l_Lean_Syntax_isNone(v___x_5627_);
                        if v___x_5628_ == 0 {
                            crate::leanh::lean_inc(v___x_5627_);
                            v___x_5629_ = l_Lean_Syntax_matchesNull(v___x_5627_, v___x_5626_);
                            if v___x_5629_ == 0 {
                                crate::leanh::lean_dec(v___x_5627_);
                                crate::leanh::lean_dec(v___x_5592_);
                                v___x_5630_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                                return v___x_5630_;
                            } else {
                                v___x_5631_ = l_Lean_Syntax_getArg(v___x_5627_, v___x_5591_);
                                crate::leanh::lean_dec(v___x_5627_);
                                v___x_5632_ = l_Lean_Syntax_getArgs(v___x_5631_);
                                crate::leanh::lean_dec(v___x_5631_);
                                v___x_5633_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_5634_ = l_Lean_Elab_LibrarySearch_evalExact___closed__4;
                                v___x_5635_ = lean_array_get_size(v___x_5632_);
                                v___x_5636_ = lean_nat_dec_lt(v___x_5633_, v___x_5635_);
                                if v___x_5636_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_5632_);
                                    v___y_5620_ = v___x_5634_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_5637_ = crate::leanh::lean_box((v___x_5594_) as usize);
                                    v___x_5638_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_5638_, 0, v___x_5637_);
                                    crate::leanh::lean_ctor_set(v___x_5638_, 1, v___x_5634_);
                                    v___x_5639_ = lean_nat_dec_le(v___x_5635_, v___x_5635_);
                                    if v___x_5639_ == 0 {
                                        if v___x_5636_ == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_5638_, 2);
                                            crate::leanh::lean_dec_ref(v___x_5632_);
                                            v___y_5620_ = v___x_5634_;
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_5640_ = 0usize;
                                            v___x_5641_ = lean_usize_of_nat(v___x_5635_);
                                            v___x_5642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5594_, v___x_5628_, v___x_5632_, v___x_5640_, v___x_5641_, v___x_5638_);
                                            crate::leanh::lean_dec_ref(v___x_5632_);
                                            v_snd_5643_ =
                                                crate::leanh::lean_ctor_get(v___x_5642_, 1);
                                            crate::leanh::lean_inc(v_snd_5643_);
                                            crate::leanh::lean_dec_ref(v___x_5642_);
                                            v___y_5620_ = v_snd_5643_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        v___x_5644_ = 0usize;
                                        v___x_5645_ = lean_usize_of_nat(v___x_5635_);
                                        v___x_5646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5594_, v___x_5628_, v___x_5632_, v___x_5644_, v___x_5645_, v___x_5638_);
                                        crate::leanh::lean_dec_ref(v___x_5632_);
                                        v_snd_5647_ = crate::leanh::lean_ctor_get(v___x_5646_, 1);
                                        crate::leanh::lean_inc(v_snd_5647_);
                                        crate::leanh::lean_dec_ref(v___x_5646_);
                                        v___y_5620_ = v_snd_5647_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_5627_);
                            v___x_5648_ = crate::leanh::lean_box(0);
                            v_required_5596_ = v___x_5648_;
                            v___y_5597_ = v_a_5579_;
                            v___y_5598_ = v_a_5580_;
                            v___y_5599_ = v_a_5581_;
                            v___y_5600_ = v_a_5582_;
                            v___y_5601_ = v_a_5583_;
                            v___y_5602_ = v_a_5584_;
                            v___y_5603_ = v_a_5585_;
                            v___y_5604_ = v_a_5586_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5605_ = 0;
                v___x_5606_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_5606_, 0 as u32, v___x_5605_);
                crate::leanh::lean_ctor_set_uint8(v___x_5606_, 1 as u32, v___x_5605_);
                crate::leanh::lean_ctor_set_uint8(v___x_5606_, 2 as u32, v___x_5594_);
                crate::leanh::lean_ctor_set_uint8(v___x_5606_, 3 as u32, v___x_5605_);
                v___x_5607_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
                    v___x_5592_,
                    v___x_5606_,
                    v___x_5594_,
                    v___y_5597_,
                    v___y_5603_,
                    v___y_5604_,
                );
                if crate::leanh::lean_obj_tag(v___x_5607_) == 0 {
                    v_a_5608_ = crate::leanh::lean_ctor_get(v___x_5607_, 0);
                    crate::leanh::lean_inc(v_a_5608_);
                    crate::leanh::lean_dec_ref_known(v___x_5607_, 1);
                    v_ref_5609_ = crate::leanh::lean_ctor_get(v___y_5603_, 5);
                    crate::leanh::lean_inc(v_ref_5609_);
                    v___x_5610_ = l_Lean_Elab_LibrarySearch_exact_x3f(
                        v_ref_5609_,
                        v_a_5608_,
                        v_required_5596_,
                        v___x_5605_,
                        v___y_5597_,
                        v___y_5598_,
                        v___y_5599_,
                        v___y_5600_,
                        v___y_5601_,
                        v___y_5602_,
                        v___y_5603_,
                        v___y_5604_,
                    );
                    return v___x_5610_;
                } else {
                    crate::leanh::lean_dec(v_required_5596_);
                    v_a_5611_ = crate::leanh::lean_ctor_get(v___x_5607_, 0);
                    v_isSharedCheck_5618_ = (!crate::leanh::lean_is_exclusive(v___x_5607_)) as u8;
                    if v_isSharedCheck_5618_ == 0 {
                        v___x_5613_ = v___x_5607_;
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5611_);
                        crate::leanh::lean_dec(v___x_5607_);
                        v___x_5613_ = crate::leanh::lean_box(0);
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5614_ == 0 {
                    v___x_5616_ = v___x_5613_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
                    v___x_5616_ = v_reuseFailAlloc_5617_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5616_;
            }
            4 => {
                v_sz_5621_ = lean_array_size(v___y_5620_);
                v___x_5622_ = 0usize;
                v___x_5623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalApply_spec__0(v_sz_5621_, v___x_5622_, v___y_5620_);
                if crate::leanh::lean_obj_tag(v___x_5623_) == 0 {
                    crate::leanh::lean_dec(v___x_5592_);
                    v___x_5624_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                    return v___x_5624_;
                } else {
                    v_required_5596_ = v___x_5623_;
                    v___y_5597_ = v_a_5579_;
                    v___y_5598_ = v_a_5580_;
                    v___y_5599_ = v_a_5581_;
                    v___y_5600_ = v_a_5582_;
                    v___y_5601_ = v_a_5583_;
                    v___y_5602_ = v_a_5584_;
                    v___y_5603_ = v_a_5585_;
                    v___y_5604_ = v_a_5586_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_evalApply___boxed(
    mut v_stx_5649_: *mut crate::leanh::LeanObject,
    mut v_a_5650_: *mut crate::leanh::LeanObject,
    mut v_a_5651_: *mut crate::leanh::LeanObject,
    mut v_a_5652_: *mut crate::leanh::LeanObject,
    mut v_a_5653_: *mut crate::leanh::LeanObject,
    mut v_a_5654_: *mut crate::leanh::LeanObject,
    mut v_a_5655_: *mut crate::leanh::LeanObject,
    mut v_a_5656_: *mut crate::leanh::LeanObject,
    mut v_a_5657_: *mut crate::leanh::LeanObject,
    mut v_a_5658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5659_ = l_Lean_Elab_LibrarySearch_evalApply(
        v_stx_5649_,
        v_a_5650_,
        v_a_5651_,
        v_a_5652_,
        v_a_5653_,
        v_a_5654_,
        v_a_5655_,
        v_a_5656_,
        v_a_5657_,
    );
    crate::leanh::lean_dec(v_a_5657_);
    crate::leanh::lean_dec_ref(v_a_5656_);
    crate::leanh::lean_dec(v_a_5655_);
    crate::leanh::lean_dec_ref(v_a_5654_);
    crate::leanh::lean_dec(v_a_5653_);
    crate::leanh::lean_dec_ref(v_a_5652_);
    crate::leanh::lean_dec(v_a_5651_);
    crate::leanh::lean_dec_ref(v_a_5650_);
    return v_res_5659_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5667_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5668_ = l_Lean_Elab_LibrarySearch_evalApply___closed__0;
    v___x_5669_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1;
    v___x_5670_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_LibrarySearch_evalApply___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_5671_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5667_,
        v___x_5668_,
        v___x_5669_,
        v___x_5670_,
    );
    return v___x_5671_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___boxed(
    mut v_a_5672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5673_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1();
    return v_res_5673_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5700_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1;
    v___x_5701_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6;
    v___x_5702_ = l_Lean_addBuiltinDeclarationRanges(v___x_5700_, v___x_5701_);
    return v___x_5702_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___boxed(
    mut v_a_5703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5704_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3();
    return v_res_5704_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5706_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0);
    v___x_5707_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5707_, 0, v___x_5706_);
    return v___x_5707_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg___boxed(
    mut v___y_5708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5709_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg();
    return v_res_5709_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0(
    mut v_00_u03b1_5710_: *mut crate::leanh::LeanObject,
    mut v___y_5711_: *mut crate::leanh::LeanObject,
    mut v___y_5712_: *mut crate::leanh::LeanObject,
    mut v___y_5713_: *mut crate::leanh::LeanObject,
    mut v___y_5714_: *mut crate::leanh::LeanObject,
    mut v___y_5715_: *mut crate::leanh::LeanObject,
    mut v___y_5716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5718_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg();
    return v___x_5718_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___boxed(
    mut v_00_u03b1_5719_: *mut crate::leanh::LeanObject,
    mut v___y_5720_: *mut crate::leanh::LeanObject,
    mut v___y_5721_: *mut crate::leanh::LeanObject,
    mut v___y_5722_: *mut crate::leanh::LeanObject,
    mut v___y_5723_: *mut crate::leanh::LeanObject,
    mut v___y_5724_: *mut crate::leanh::LeanObject,
    mut v___y_5725_: *mut crate::leanh::LeanObject,
    mut v___y_5726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0(v_00_u03b1_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
    crate::leanh::lean_dec(v___y_5725_);
    crate::leanh::lean_dec_ref(v___y_5724_);
    crate::leanh::lean_dec(v___y_5723_);
    crate::leanh::lean_dec_ref(v___y_5722_);
    crate::leanh::lean_dec(v___y_5721_);
    crate::leanh::lean_dec_ref(v___y_5720_);
    return v_res_5727_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0(
    mut v_x_5728_: *mut crate::leanh::LeanObject,
    mut v___y_5729_: *mut crate::leanh::LeanObject,
    mut v___y_5730_: *mut crate::leanh::LeanObject,
    mut v___y_5731_: *mut crate::leanh::LeanObject,
    mut v___y_5732_: *mut crate::leanh::LeanObject,
    mut v___y_5733_: *mut crate::leanh::LeanObject,
    mut v___y_5734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5730_);
    crate::leanh::lean_inc_ref(v___y_5729_);
    v___x_5736_ = crate::leanh::lean_apply_7(
        v_x_5728_,
        v___y_5729_,
        v___y_5730_,
        v___y_5731_,
        v___y_5732_,
        v___y_5733_,
        v___y_5734_,
        crate::leanh::lean_box(0),
    );
    return v___x_5736_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0___boxed(
    mut v_x_5737_: *mut crate::leanh::LeanObject,
    mut v___y_5738_: *mut crate::leanh::LeanObject,
    mut v___y_5739_: *mut crate::leanh::LeanObject,
    mut v___y_5740_: *mut crate::leanh::LeanObject,
    mut v___y_5741_: *mut crate::leanh::LeanObject,
    mut v___y_5742_: *mut crate::leanh::LeanObject,
    mut v___y_5743_: *mut crate::leanh::LeanObject,
    mut v___y_5744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5745_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0(v_x_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
    crate::leanh::lean_dec(v___y_5739_);
    crate::leanh::lean_dec_ref(v___y_5738_);
    return v_res_5745_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(
    mut v_mvarId_5746_: *mut crate::leanh::LeanObject,
    mut v_x_5747_: *mut crate::leanh::LeanObject,
    mut v___y_5748_: *mut crate::leanh::LeanObject,
    mut v___y_5749_: *mut crate::leanh::LeanObject,
    mut v___y_5750_: *mut crate::leanh::LeanObject,
    mut v___y_5751_: *mut crate::leanh::LeanObject,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5760_: u8 = 0;
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5749_);
                crate::leanh::lean_inc_ref(v___y_5748_);
                v___f_5755_ = crate::leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___f_5755_, 0, v_x_5747_);
                crate::leanh::lean_closure_set(v___f_5755_, 1, v___y_5748_);
                crate::leanh::lean_closure_set(v___f_5755_, 2, v___y_5749_);
                v___x_5756_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5746_,
                    v___f_5755_,
                    v___y_5750_,
                    v___y_5751_,
                    v___y_5752_,
                    v___y_5753_,
                );
                if crate::leanh::lean_obj_tag(v___x_5756_) == 0 {
                    return v___x_5756_;
                } else {
                    v_a_5757_ = crate::leanh::lean_ctor_get(v___x_5756_, 0);
                    v_isSharedCheck_5764_ = (!crate::leanh::lean_is_exclusive(v___x_5756_)) as u8;
                    if v_isSharedCheck_5764_ == 0 {
                        v___x_5759_ = v___x_5756_;
                        v_isShared_5760_ = v_isSharedCheck_5764_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5757_);
                        crate::leanh::lean_dec(v___x_5756_);
                        v___x_5759_ = crate::leanh::lean_box(0);
                        v_isShared_5760_ = v_isSharedCheck_5764_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5760_ == 0 {
                    v___x_5762_ = v___x_5759_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5763_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
                    v___x_5762_ = v_reuseFailAlloc_5763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___boxed(
    mut v_mvarId_5765_: *mut crate::leanh::LeanObject,
    mut v_x_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
    mut v___y_5768_: *mut crate::leanh::LeanObject,
    mut v___y_5769_: *mut crate::leanh::LeanObject,
    mut v___y_5770_: *mut crate::leanh::LeanObject,
    mut v___y_5771_: *mut crate::leanh::LeanObject,
    mut v___y_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5774_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(v_mvarId_5765_, v_x_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
    crate::leanh::lean_dec(v___y_5772_);
    crate::leanh::lean_dec_ref(v___y_5771_);
    crate::leanh::lean_dec(v___y_5770_);
    crate::leanh::lean_dec_ref(v___y_5769_);
    crate::leanh::lean_dec(v___y_5768_);
    crate::leanh::lean_dec_ref(v___y_5767_);
    return v_res_5774_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2(
    mut v_00_u03b1_5775_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5776_: *mut crate::leanh::LeanObject,
    mut v_x_5777_: *mut crate::leanh::LeanObject,
    mut v___y_5778_: *mut crate::leanh::LeanObject,
    mut v___y_5779_: *mut crate::leanh::LeanObject,
    mut v___y_5780_: *mut crate::leanh::LeanObject,
    mut v___y_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5785_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(v_mvarId_5776_, v_x_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
    return v___x_5785_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___boxed(
    mut v_00_u03b1_5786_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5787_: *mut crate::leanh::LeanObject,
    mut v_x_5788_: *mut crate::leanh::LeanObject,
    mut v___y_5789_: *mut crate::leanh::LeanObject,
    mut v___y_5790_: *mut crate::leanh::LeanObject,
    mut v___y_5791_: *mut crate::leanh::LeanObject,
    mut v___y_5792_: *mut crate::leanh::LeanObject,
    mut v___y_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5796_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2(
            v_00_u03b1_5786_,
            v_mvarId_5787_,
            v_x_5788_,
            v___y_5789_,
            v___y_5790_,
            v___y_5791_,
            v___y_5792_,
            v___y_5793_,
            v___y_5794_,
        );
    crate::leanh::lean_dec(v___y_5794_);
    crate::leanh::lean_dec_ref(v___y_5793_);
    crate::leanh::lean_dec(v___y_5792_);
    crate::leanh::lean_dec_ref(v___y_5791_);
    crate::leanh::lean_dec(v___y_5790_);
    crate::leanh::lean_dec_ref(v___y_5789_);
    return v_res_5796_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__0(
    mut v_g_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
    mut v___y_5801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: u8 = 0;
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5803_ = crate::leanh::lean_box(0);
    v___x_5804_ = 0;
    v___x_5805_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_5806_ = l_Lean_Meta_LibrarySearch_solveByElim(
        v___x_5803_,
        v___x_5804_,
        v_g_5797_,
        v___x_5805_,
        v___x_5804_,
        v___x_5804_,
        v___y_5798_,
        v___y_5799_,
        v___y_5800_,
        v___y_5801_,
    );
    return v___x_5806_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__0___boxed(
    mut v_g_5807_: *mut crate::leanh::LeanObject,
    mut v___y_5808_: *mut crate::leanh::LeanObject,
    mut v___y_5809_: *mut crate::leanh::LeanObject,
    mut v___y_5810_: *mut crate::leanh::LeanObject,
    mut v___y_5811_: *mut crate::leanh::LeanObject,
    mut v___y_5812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5813_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__0(
        v_g_5807_,
        v___y_5808_,
        v___y_5809_,
        v___y_5810_,
        v___y_5811_,
    );
    crate::leanh::lean_dec(v___y_5811_);
    crate::leanh::lean_dec_ref(v___y_5810_);
    crate::leanh::lean_dec(v___y_5809_);
    crate::leanh::lean_dec_ref(v___y_5808_);
    return v_res_5813_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1(
    mut v___x_5814_: u8,
    mut v_x_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
    mut v___y_5817_: *mut crate::leanh::LeanObject,
    mut v___y_5818_: *mut crate::leanh::LeanObject,
    mut v___y_5819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5821_ = crate::leanh::lean_box((v___x_5814_) as usize);
    v___x_5822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5822_, 0, v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1___boxed(
    mut v___x_5823_: *mut crate::leanh::LeanObject,
    mut v_x_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
    mut v___y_5826_: *mut crate::leanh::LeanObject,
    mut v___y_5827_: *mut crate::leanh::LeanObject,
    mut v___y_5828_: *mut crate::leanh::LeanObject,
    mut v___y_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6766__boxed_5830_: u8 = 0;
    let mut v_res_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6766__boxed_5830_ = (crate::leanh::lean_unbox(v___x_5823_) as u8);
    v_res_5831_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1(
        v___x_6766__boxed_5830_,
        v_x_5824_,
        v___y_5825_,
        v___y_5826_,
        v___y_5827_,
        v___y_5828_,
    );
    crate::leanh::lean_dec(v___y_5828_);
    crate::leanh::lean_dec_ref(v___y_5827_);
    crate::leanh::lean_dec(v___y_5826_);
    crate::leanh::lean_dec_ref(v___y_5825_);
    crate::leanh::lean_dec(v_x_5824_);
    return v_res_5831_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(
    mut v_ref_5832_: *mut crate::leanh::LeanObject,
    mut v_msgData_5833_: *mut crate::leanh::LeanObject,
    mut v_severity_5834_: u8,
    mut v_isSilent_5835_: u8,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5845_: u8 = 0;
    let mut v___y_5846_: u8 = 0;
    let mut v___y_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5865_: u8 = 0;
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut v___y_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5881_: u8 = 0;
    let mut v___y_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5883_: u8 = 0;
    let mut v___y_5884_: u8 = 0;
    let mut v___y_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: u8 = 0;
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5901_: u8 = 0;
    let mut v___y_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: u8 = 0;
    let mut v___y_5908_: u8 = 0;
    let mut v___y_5909_: u8 = 0;
    let mut v___y_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5917_: u8 = 0;
    let mut v___y_5918_: u8 = 0;
    let mut v___y_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5920_: u8 = 0;
    let mut v_ref_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: u8 = 0;
    let mut v___y_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: u8 = 0;
    let mut v___y_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: u8 = 0;
    let mut v___y_5933_: u8 = 0;
    let mut v___y_5935_: u8 = 0;
    let mut v_fileName_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5940_: u8 = 0;
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: u8 = 0;
    let mut v___x_5945_: u8 = 0;
    let mut v___x_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: u8 = 0;
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: u8 = 0;
    let mut v___x_5951_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5925_ = 2;
                v___x_5950_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5834_, v___x_5925_);
                if v___x_5950_ == 0 {
                    v___y_5935_ = v___x_5950_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_5833_);
                    v___x_5951_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5833_);
                    v___y_5935_ = v___x_5951_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5851_ = lean_st_ref_take(v___y_5850_);
                v_currNamespace_5852_ = crate::leanh::lean_ctor_get(v___y_5849_, 6);
                v_openDecls_5853_ = crate::leanh::lean_ctor_get(v___y_5849_, 7);
                v_env_5854_ = crate::leanh::lean_ctor_get(v___x_5851_, 0);
                v_nextMacroScope_5855_ = crate::leanh::lean_ctor_get(v___x_5851_, 1);
                v_ngen_5856_ = crate::leanh::lean_ctor_get(v___x_5851_, 2);
                v_auxDeclNGen_5857_ = crate::leanh::lean_ctor_get(v___x_5851_, 3);
                v_traceState_5858_ = crate::leanh::lean_ctor_get(v___x_5851_, 4);
                v_cache_5859_ = crate::leanh::lean_ctor_get(v___x_5851_, 5);
                v_messages_5860_ = crate::leanh::lean_ctor_get(v___x_5851_, 6);
                v_infoState_5861_ = crate::leanh::lean_ctor_get(v___x_5851_, 7);
                v_snapshotTasks_5862_ = crate::leanh::lean_ctor_get(v___x_5851_, 8);
                v_isSharedCheck_5876_ = (!crate::leanh::lean_is_exclusive(v___x_5851_)) as u8;
                if v_isSharedCheck_5876_ == 0 {
                    v___x_5864_ = v___x_5851_;
                    v_isShared_5865_ = v_isSharedCheck_5876_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5862_);
                    crate::leanh::lean_inc(v_infoState_5861_);
                    crate::leanh::lean_inc(v_messages_5860_);
                    crate::leanh::lean_inc(v_cache_5859_);
                    crate::leanh::lean_inc(v_traceState_5858_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5857_);
                    crate::leanh::lean_inc(v_ngen_5856_);
                    crate::leanh::lean_inc(v_nextMacroScope_5855_);
                    crate::leanh::lean_inc(v_env_5854_);
                    crate::leanh::lean_dec(v___x_5851_);
                    v___x_5864_ = crate::leanh::lean_box(0);
                    v_isShared_5865_ = v_isSharedCheck_5876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_5853_);
                crate::leanh::lean_inc(v_currNamespace_5852_);
                v___x_5866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5866_, 0, v_currNamespace_5852_);
                crate::leanh::lean_ctor_set(v___x_5866_, 1, v_openDecls_5853_);
                v___x_5867_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5867_, 0, v___x_5866_);
                crate::leanh::lean_ctor_set(v___x_5867_, 1, v___y_5844_);
                crate::leanh::lean_inc_ref(v___y_5847_);
                crate::leanh::lean_inc_ref(v___y_5843_);
                v___x_5868_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5868_, 0, v___y_5843_);
                crate::leanh::lean_ctor_set(v___x_5868_, 1, v___y_5848_);
                crate::leanh::lean_ctor_set(v___x_5868_, 2, v___y_5842_);
                crate::leanh::lean_ctor_set(v___x_5868_, 3, v___y_5847_);
                crate::leanh::lean_ctor_set(v___x_5868_, 4, v___x_5867_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5868_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_5846_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5868_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5845_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5868_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5835_,
                );
                v___x_5869_ = l_Lean_MessageLog_add(v___x_5868_, v_messages_5860_);
                if v_isShared_5865_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5864_, 6, v___x_5869_);
                    v___x_5871_ = v___x_5864_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_env_5854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 1, v_nextMacroScope_5855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_ngen_5856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 3, v_auxDeclNGen_5857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 4, v_traceState_5858_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 5, v_cache_5859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 6, v___x_5869_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 7, v_infoState_5861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5875_, 8, v_snapshotTasks_5862_);
                    v___x_5871_ = v_reuseFailAlloc_5875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5872_ = lean_st_ref_set(v___y_5850_, v___x_5871_);
                v___x_5873_ = crate::leanh::lean_box(0);
                v___x_5874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5874_, 0, v___x_5873_);
                return v___x_5874_;
            }
            4 => {
                v___x_5886_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5833_,
                    );
                v___x_5887_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v___x_5886_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
                v_a_5888_ = crate::leanh::lean_ctor_get(v___x_5887_, 0);
                v_isSharedCheck_5901_ = (!crate::leanh::lean_is_exclusive(v___x_5887_)) as u8;
                if v_isSharedCheck_5901_ == 0 {
                    v___x_5890_ = v___x_5887_;
                    v_isShared_5891_ = v_isSharedCheck_5901_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5888_);
                    crate::leanh::lean_dec(v___x_5887_);
                    v___x_5890_ = crate::leanh::lean_box(0);
                    v_isShared_5891_ = v_isSharedCheck_5901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_5880_, 2);
                v___x_5892_ = l_Lean_FileMap_toPosition(v___y_5880_, v___y_5882_);
                crate::leanh::lean_dec(v___y_5882_);
                v___x_5893_ = l_Lean_FileMap_toPosition(v___y_5880_, v___y_5885_);
                crate::leanh::lean_dec(v___y_5885_);
                v___x_5894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5894_, 0, v___x_5893_);
                v___x_5895_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0;
                if v___y_5881_ == 0 {
                    crate::leanh::lean_del_object(v___x_5890_);
                    crate::leanh::lean_dec_ref(v___y_5878_);
                    v___y_5842_ = v___x_5894_;
                    v___y_5843_ = v___y_5879_;
                    v___y_5844_ = v_a_5888_;
                    v___y_5845_ = v___y_5883_;
                    v___y_5846_ = v___y_5884_;
                    v___y_5847_ = v___x_5895_;
                    v___y_5848_ = v___x_5892_;
                    v___y_5849_ = v___y_5838_;
                    v___y_5850_ = v___y_5839_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5888_);
                    v___x_5896_ = l_Lean_MessageData_hasTag(v___y_5878_, v_a_5888_);
                    if v___x_5896_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5894_, 1);
                        crate::leanh::lean_dec_ref(v___x_5892_);
                        crate::leanh::lean_dec(v_a_5888_);
                        v___x_5897_ = crate::leanh::lean_box(0);
                        if v_isShared_5891_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5890_, 0, v___x_5897_);
                            v___x_5899_ = v___x_5890_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5900_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5897_);
                            v___x_5899_ = v_reuseFailAlloc_5900_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5890_);
                        v___y_5842_ = v___x_5894_;
                        v___y_5843_ = v___y_5879_;
                        v___y_5844_ = v_a_5888_;
                        v___y_5845_ = v___y_5883_;
                        v___y_5846_ = v___y_5884_;
                        v___y_5847_ = v___x_5895_;
                        v___y_5848_ = v___x_5892_;
                        v___y_5849_ = v___y_5838_;
                        v___y_5850_ = v___y_5839_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5899_;
            }
            7 => {
                v___x_5911_ = l_Lean_Syntax_getTailPos_x3f(v___y_5905_, v___y_5909_);
                crate::leanh::lean_dec(v___y_5905_);
                if crate::leanh::lean_obj_tag(v___x_5911_) == 0 {
                    crate::leanh::lean_inc(v___y_5910_);
                    v___y_5878_ = v___y_5903_;
                    v___y_5879_ = v___y_5904_;
                    v___y_5880_ = v___y_5906_;
                    v___y_5881_ = v___y_5907_;
                    v___y_5882_ = v___y_5910_;
                    v___y_5883_ = v___y_5908_;
                    v___y_5884_ = v___y_5909_;
                    v___y_5885_ = v___y_5910_;
                    state = 4;
                    continue;
                } else {
                    v_val_5912_ = crate::leanh::lean_ctor_get(v___x_5911_, 0);
                    crate::leanh::lean_inc(v_val_5912_);
                    crate::leanh::lean_dec_ref_known(v___x_5911_, 1);
                    v___y_5878_ = v___y_5903_;
                    v___y_5879_ = v___y_5904_;
                    v___y_5880_ = v___y_5906_;
                    v___y_5881_ = v___y_5907_;
                    v___y_5882_ = v___y_5910_;
                    v___y_5883_ = v___y_5908_;
                    v___y_5884_ = v___y_5909_;
                    v___y_5885_ = v_val_5912_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_5921_ = l_Lean_replaceRef(v_ref_5832_, v___y_5919_);
                v___x_5922_ = l_Lean_Syntax_getPos_x3f(v_ref_5921_, v___y_5918_);
                if crate::leanh::lean_obj_tag(v___x_5922_) == 0 {
                    v___x_5923_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5903_ = v___y_5914_;
                    v___y_5904_ = v___y_5915_;
                    v___y_5905_ = v_ref_5921_;
                    v___y_5906_ = v___y_5916_;
                    v___y_5907_ = v___y_5917_;
                    v___y_5908_ = v___y_5920_;
                    v___y_5909_ = v___y_5918_;
                    v___y_5910_ = v___x_5923_;
                    state = 7;
                    continue;
                } else {
                    v_val_5924_ = crate::leanh::lean_ctor_get(v___x_5922_, 0);
                    crate::leanh::lean_inc(v_val_5924_);
                    crate::leanh::lean_dec_ref_known(v___x_5922_, 1);
                    v___y_5903_ = v___y_5914_;
                    v___y_5904_ = v___y_5915_;
                    v___y_5905_ = v_ref_5921_;
                    v___y_5906_ = v___y_5916_;
                    v___y_5907_ = v___y_5917_;
                    v___y_5908_ = v___y_5920_;
                    v___y_5909_ = v___y_5918_;
                    v___y_5910_ = v_val_5924_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_5933_ == 0 {
                    v___y_5914_ = v___y_5930_;
                    v___y_5915_ = v___y_5927_;
                    v___y_5916_ = v___y_5928_;
                    v___y_5917_ = v___y_5929_;
                    v___y_5918_ = v___y_5932_;
                    v___y_5919_ = v___y_5931_;
                    v___y_5920_ = v_severity_5834_;
                    state = 8;
                    continue;
                } else {
                    v___y_5914_ = v___y_5930_;
                    v___y_5915_ = v___y_5927_;
                    v___y_5916_ = v___y_5928_;
                    v___y_5917_ = v___y_5929_;
                    v___y_5918_ = v___y_5932_;
                    v___y_5919_ = v___y_5931_;
                    v___y_5920_ = v___x_5925_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_5935_ == 0 {
                    v_fileName_5936_ = crate::leanh::lean_ctor_get(v___y_5838_, 0);
                    v_fileMap_5937_ = crate::leanh::lean_ctor_get(v___y_5838_, 1);
                    v_options_5938_ = crate::leanh::lean_ctor_get(v___y_5838_, 2);
                    v_ref_5939_ = crate::leanh::lean_ctor_get(v___y_5838_, 5);
                    v_suppressElabErrors_5940_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_5838_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5941_ = crate::leanh::lean_box((v___y_5935_) as usize);
                    v___x_5942_ = crate::leanh::lean_box((v_suppressElabErrors_5940_) as usize);
                    v___f_5943_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5943_, 0, v___x_5941_);
                    crate::leanh::lean_closure_set(v___f_5943_, 1, v___x_5942_);
                    v___x_5944_ = 1;
                    v___x_5945_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5834_, v___x_5944_);
                    if v___x_5945_ == 0 {
                        v___y_5927_ = v_fileName_5936_;
                        v___y_5928_ = v_fileMap_5937_;
                        v___y_5929_ = v_suppressElabErrors_5940_;
                        v___y_5930_ = v___f_5943_;
                        v___y_5931_ = v_ref_5939_;
                        v___y_5932_ = v___y_5935_;
                        v___y_5933_ = v___x_5945_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5946_ = l_Lean_warningAsError;
                        v___x_5947_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_5938_, v___x_5946_);
                        v___y_5927_ = v_fileName_5936_;
                        v___y_5928_ = v_fileMap_5937_;
                        v___y_5929_ = v_suppressElabErrors_5940_;
                        v___y_5930_ = v___f_5943_;
                        v___y_5931_ = v_ref_5939_;
                        v___y_5932_ = v___y_5935_;
                        v___y_5933_ = v___x_5947_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_5833_);
                    v___x_5948_ = crate::leanh::lean_box(0);
                    v___x_5949_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5949_, 0, v___x_5948_);
                    return v___x_5949_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_ref_5952_: *mut crate::leanh::LeanObject,
    mut v_msgData_5953_: *mut crate::leanh::LeanObject,
    mut v_severity_5954_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5955_: *mut crate::leanh::LeanObject,
    mut v___y_5956_: *mut crate::leanh::LeanObject,
    mut v___y_5957_: *mut crate::leanh::LeanObject,
    mut v___y_5958_: *mut crate::leanh::LeanObject,
    mut v___y_5959_: *mut crate::leanh::LeanObject,
    mut v___y_5960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5961_: u8 = 0;
    let mut v_isSilent_boxed_5962_: u8 = 0;
    let mut v_res_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5961_ = (crate::leanh::lean_unbox(v_severity_5954_) as u8);
    v_isSilent_boxed_5962_ = (crate::leanh::lean_unbox(v_isSilent_5955_) as u8);
    v_res_5963_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(v_ref_5952_, v_msgData_5953_, v_severity_boxed_5961_, v_isSilent_boxed_5962_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_);
    crate::leanh::lean_dec(v___y_5959_);
    crate::leanh::lean_dec_ref(v___y_5958_);
    crate::leanh::lean_dec(v___y_5957_);
    crate::leanh::lean_dec_ref(v___y_5956_);
    crate::leanh::lean_dec(v_ref_5952_);
    return v_res_5963_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1(
    mut v_msgData_5964_: *mut crate::leanh::LeanObject,
    mut v_severity_5965_: u8,
    mut v_isSilent_5966_: u8,
    mut v___y_5967_: *mut crate::leanh::LeanObject,
    mut v___y_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
    mut v___y_5970_: *mut crate::leanh::LeanObject,
    mut v___y_5971_: *mut crate::leanh::LeanObject,
    mut v___y_5972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_5974_ = crate::leanh::lean_ctor_get(v___y_5971_, 5);
    v___x_5975_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(v_ref_5974_, v_msgData_5964_, v_severity_5965_, v_isSilent_5966_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
    return v___x_5975_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1___boxed(
    mut v_msgData_5976_: *mut crate::leanh::LeanObject,
    mut v_severity_5977_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5978_: *mut crate::leanh::LeanObject,
    mut v___y_5979_: *mut crate::leanh::LeanObject,
    mut v___y_5980_: *mut crate::leanh::LeanObject,
    mut v___y_5981_: *mut crate::leanh::LeanObject,
    mut v___y_5982_: *mut crate::leanh::LeanObject,
    mut v___y_5983_: *mut crate::leanh::LeanObject,
    mut v___y_5984_: *mut crate::leanh::LeanObject,
    mut v___y_5985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5986_: u8 = 0;
    let mut v_isSilent_boxed_5987_: u8 = 0;
    let mut v_res_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5986_ = (crate::leanh::lean_unbox(v_severity_5977_) as u8);
    v_isSilent_boxed_5987_ = (crate::leanh::lean_unbox(v_isSilent_5978_) as u8);
    v_res_5988_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1(v_msgData_5976_, v_severity_boxed_5986_, v_isSilent_boxed_5987_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
    crate::leanh::lean_dec(v___y_5984_);
    crate::leanh::lean_dec_ref(v___y_5983_);
    crate::leanh::lean_dec(v___y_5982_);
    crate::leanh::lean_dec_ref(v___y_5981_);
    crate::leanh::lean_dec(v___y_5980_);
    crate::leanh::lean_dec_ref(v___y_5979_);
    return v_res_5988_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(
    mut v_msgData_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
    mut v___y_5991_: *mut crate::leanh::LeanObject,
    mut v___y_5992_: *mut crate::leanh::LeanObject,
    mut v___y_5993_: *mut crate::leanh::LeanObject,
    mut v___y_5994_: *mut crate::leanh::LeanObject,
    mut v___y_5995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5997_: u8 = 0;
    let mut v___x_5998_: u8 = 0;
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5997_ = 2;
    v___x_5998_ = 0;
    v___x_5999_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1(v_msgData_5989_, v___x_5997_, v___x_5998_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
    return v___x_5999_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1___boxed(
    mut v_msgData_6000_: *mut crate::leanh::LeanObject,
    mut v___y_6001_: *mut crate::leanh::LeanObject,
    mut v___y_6002_: *mut crate::leanh::LeanObject,
    mut v___y_6003_: *mut crate::leanh::LeanObject,
    mut v___y_6004_: *mut crate::leanh::LeanObject,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6008_ = l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(
        v_msgData_6000_,
        v___y_6001_,
        v___y_6002_,
        v___y_6003_,
        v___y_6004_,
        v___y_6005_,
        v___y_6006_,
    );
    crate::leanh::lean_dec(v___y_6006_);
    crate::leanh::lean_dec_ref(v___y_6005_);
    crate::leanh::lean_dec(v___y_6004_);
    crate::leanh::lean_dec_ref(v___y_6003_);
    crate::leanh::lean_dec(v___y_6002_);
    crate::leanh::lean_dec_ref(v___y_6001_);
    return v_res_6008_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6012_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1;
    v___x_6013_ = l_Lean_MessageData_ofFormat(v___x_6012_);
    return v___x_6013_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6017_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4;
    v___x_6018_ = l_Lean_MessageData_ofFormat(v___x_6017_);
    return v___x_6018_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2(
    mut v_snd_6020_: *mut crate::leanh::LeanObject,
    mut v___f_6021_: *mut crate::leanh::LeanObject,
    mut v___f_6022_: *mut crate::leanh::LeanObject,
    mut v___x_6023_: *mut crate::leanh::LeanObject,
    mut v___x_6024_: u8,
    mut v___x_6025_: u8,
    mut v_expectedType_6026_: *mut crate::leanh::LeanObject,
    mut v_a_6027_: *mut crate::leanh::LeanObject,
    mut v_stx_6028_: *mut crate::leanh::LeanObject,
    mut v___y_6029_: *mut crate::leanh::LeanObject,
    mut v___y_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
    mut v___y_6033_: *mut crate::leanh::LeanObject,
    mut v___y_6034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: u8 = 0;
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6048_: u8 = 0;
    let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6074_: u8 = 0;
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6078_: u8 = 0;
    let mut v_a_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6036_ = l_Lean_Meta_LibrarySearch_librarySearch(
                    v_snd_6020_,
                    v___f_6021_,
                    v___f_6022_,
                    v___x_6023_,
                    v___x_6024_,
                    v___x_6025_,
                    v___y_6031_,
                    v___y_6032_,
                    v___y_6033_,
                    v___y_6034_,
                );
                if crate::leanh::lean_obj_tag(v___x_6036_) == 0 {
                    v_a_6037_ = crate::leanh::lean_ctor_get(v___x_6036_, 0);
                    crate::leanh::lean_inc(v_a_6037_);
                    crate::leanh::lean_dec_ref_known(v___x_6036_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6037_) == 1 {
                        crate::leanh::lean_dec(v_stx_6028_);
                        crate::leanh::lean_dec_ref(v_a_6027_);
                        v_val_6038_ = crate::leanh::lean_ctor_get(v_a_6037_, 0);
                        crate::leanh::lean_inc(v_val_6038_);
                        crate::leanh::lean_dec_ref_known(v_a_6037_, 1);
                        v___x_6039_ = lean_array_get_size(v_val_6038_);
                        crate::leanh::lean_dec(v_val_6038_);
                        v___x_6040_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6041_ = lean_nat_dec_eq(v___x_6039_, v___x_6040_);
                        if v___x_6041_ == 0 {
                            v___x_6042_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2_once), _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2);
                            v___x_6043_ = l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(v___x_6042_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
                            if crate::leanh::lean_obj_tag(v___x_6043_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6043_, 1);
                                v___x_6044_ = l_Lean_Meta_mkLabeledSorry(
                                    v_expectedType_6026_,
                                    v___x_6024_,
                                    v___x_6024_,
                                    v___y_6031_,
                                    v___y_6032_,
                                    v___y_6033_,
                                    v___y_6034_,
                                );
                                return v___x_6044_;
                            } else {
                                crate::leanh::lean_dec_ref(v_expectedType_6026_);
                                v_a_6045_ = crate::leanh::lean_ctor_get(v___x_6043_, 0);
                                v_isSharedCheck_6052_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6043_)) as u8;
                                if v_isSharedCheck_6052_ == 0 {
                                    v___x_6047_ = v___x_6043_;
                                    v_isShared_6048_ = v_isSharedCheck_6052_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6045_);
                                    crate::leanh::lean_dec(v___x_6043_);
                                    v___x_6047_ = crate::leanh::lean_box(0);
                                    v_isShared_6048_ = v_isSharedCheck_6052_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_6053_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5_once), _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5);
                            v___x_6054_ = l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(v___x_6053_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
                            if crate::leanh::lean_obj_tag(v___x_6054_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6054_, 1);
                                v___x_6055_ = l_Lean_Meta_mkLabeledSorry(
                                    v_expectedType_6026_,
                                    v___x_6024_,
                                    v___x_6024_,
                                    v___y_6031_,
                                    v___y_6032_,
                                    v___y_6033_,
                                    v___y_6034_,
                                );
                                return v___x_6055_;
                            } else {
                                crate::leanh::lean_dec_ref(v_expectedType_6026_);
                                v_a_6056_ = crate::leanh::lean_ctor_get(v___x_6054_, 0);
                                v_isSharedCheck_6063_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6054_)) as u8;
                                if v_isSharedCheck_6063_ == 0 {
                                    v___x_6058_ = v___x_6054_;
                                    v_isShared_6059_ = v_isSharedCheck_6063_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6056_);
                                    crate::leanh::lean_dec(v___x_6054_);
                                    v___x_6058_ = crate::leanh::lean_box(0);
                                    v_isShared_6059_ = v_isSharedCheck_6063_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6037_);
                        crate::leanh::lean_dec_ref(v_expectedType_6026_);
                        crate::leanh::lean_inc_ref(v_a_6027_);
                        v___x_6064_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_6027_, v___y_6032_);
                        v_a_6065_ = crate::leanh::lean_ctor_get(v___x_6064_, 0);
                        crate::leanh::lean_inc(v_a_6065_);
                        crate::leanh::lean_dec_ref(v___x_6064_);
                        v___x_6066_ = l_Lean_Expr_headBeta(v_a_6065_);
                        v___x_6067_ = crate::leanh::lean_box(0);
                        v___x_6068_ =
                            l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__6;
                        v___x_6069_ = l_Lean_Meta_Tactic_TryThis_addTermSuggestion(
                            v_stx_6028_,
                            v___x_6066_,
                            v___x_6067_,
                            v___x_6068_,
                            v___x_6067_,
                            v___y_6031_,
                            v___y_6032_,
                            v___y_6033_,
                            v___y_6034_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6069_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6069_, 1);
                            v___x_6070_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_6027_, v___y_6032_);
                            return v___x_6070_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_6027_);
                            v_a_6071_ = crate::leanh::lean_ctor_get(v___x_6069_, 0);
                            v_isSharedCheck_6078_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6069_)) as u8;
                            if v_isSharedCheck_6078_ == 0 {
                                v___x_6073_ = v___x_6069_;
                                v_isShared_6074_ = v_isSharedCheck_6078_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6071_);
                                crate::leanh::lean_dec(v___x_6069_);
                                v___x_6073_ = crate::leanh::lean_box(0);
                                v_isShared_6074_ = v_isSharedCheck_6078_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_6028_);
                    crate::leanh::lean_dec_ref(v_a_6027_);
                    crate::leanh::lean_dec_ref(v_expectedType_6026_);
                    v_a_6079_ = crate::leanh::lean_ctor_get(v___x_6036_, 0);
                    v_isSharedCheck_6086_ = (!crate::leanh::lean_is_exclusive(v___x_6036_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v___x_6081_ = v___x_6036_;
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6079_);
                        crate::leanh::lean_dec(v___x_6036_);
                        v___x_6081_ = crate::leanh::lean_box(0);
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6048_ == 0 {
                    v___x_6050_ = v___x_6047_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
                    v___x_6050_ = v_reuseFailAlloc_6051_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6050_;
            }
            3 => {
                if v_isShared_6059_ == 0 {
                    v___x_6061_ = v___x_6058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
                    v___x_6061_ = v_reuseFailAlloc_6062_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6061_;
            }
            5 => {
                if v_isShared_6074_ == 0 {
                    v___x_6076_ = v___x_6073_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_a_6071_);
                    v___x_6076_ = v_reuseFailAlloc_6077_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6076_;
            }
            7 => {
                if v_isShared_6082_ == 0 {
                    v___x_6084_ = v___x_6081_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_a_6079_);
                    v___x_6084_ = v_reuseFailAlloc_6085_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___boxed(
    mut v_snd_6087_: *mut crate::leanh::LeanObject,
    mut v___f_6088_: *mut crate::leanh::LeanObject,
    mut v___f_6089_: *mut crate::leanh::LeanObject,
    mut v___x_6090_: *mut crate::leanh::LeanObject,
    mut v___x_6091_: *mut crate::leanh::LeanObject,
    mut v___x_6092_: *mut crate::leanh::LeanObject,
    mut v_expectedType_6093_: *mut crate::leanh::LeanObject,
    mut v_a_6094_: *mut crate::leanh::LeanObject,
    mut v_stx_6095_: *mut crate::leanh::LeanObject,
    mut v___y_6096_: *mut crate::leanh::LeanObject,
    mut v___y_6097_: *mut crate::leanh::LeanObject,
    mut v___y_6098_: *mut crate::leanh::LeanObject,
    mut v___y_6099_: *mut crate::leanh::LeanObject,
    mut v___y_6100_: *mut crate::leanh::LeanObject,
    mut v___y_6101_: *mut crate::leanh::LeanObject,
    mut v___y_6102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7080__boxed_6103_: u8 = 0;
    let mut v___x_7081__boxed_6104_: u8 = 0;
    let mut v_res_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7080__boxed_6103_ = (crate::leanh::lean_unbox(v___x_6091_) as u8);
    v___x_7081__boxed_6104_ = (crate::leanh::lean_unbox(v___x_6092_) as u8);
    v_res_6105_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2(
        v_snd_6087_,
        v___f_6088_,
        v___f_6089_,
        v___x_6090_,
        v___x_7080__boxed_6103_,
        v___x_7081__boxed_6104_,
        v_expectedType_6093_,
        v_a_6094_,
        v_stx_6095_,
        v___y_6096_,
        v___y_6097_,
        v___y_6098_,
        v___y_6099_,
        v___y_6100_,
        v___y_6101_,
    );
    crate::leanh::lean_dec(v___y_6101_);
    crate::leanh::lean_dec_ref(v___y_6100_);
    crate::leanh::lean_dec(v___y_6099_);
    crate::leanh::lean_dec_ref(v___y_6098_);
    crate::leanh::lean_dec(v___y_6097_);
    crate::leanh::lean_dec_ref(v___y_6096_);
    return v_res_6105_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__3(
    mut v___f_6106_: *mut crate::leanh::LeanObject,
    mut v___f_6107_: *mut crate::leanh::LeanObject,
    mut v___x_6108_: u8,
    mut v_stx_6109_: *mut crate::leanh::LeanObject,
    mut v_expectedType_6110_: *mut crate::leanh::LeanObject,
    mut v___y_6111_: *mut crate::leanh::LeanObject,
    mut v___y_6112_: *mut crate::leanh::LeanObject,
    mut v___y_6113_: *mut crate::leanh::LeanObject,
    mut v___y_6114_: *mut crate::leanh::LeanObject,
    mut v___y_6115_: *mut crate::leanh::LeanObject,
    mut v___y_6116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: u8 = 0;
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: u8 = 0;
    let mut v___x_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6136_: u8 = 0;
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_expectedType_6110_);
                v___x_6118_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6118_, 0, v_expectedType_6110_);
                v___x_6119_ = 0;
                v___x_6120_ = crate::leanh::lean_box(0);
                v___x_6121_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_6118_,
                    v___x_6119_,
                    v___x_6120_,
                    v___y_6113_,
                    v___y_6114_,
                    v___y_6115_,
                    v___y_6116_,
                );
                if crate::leanh::lean_obj_tag(v___x_6121_) == 0 {
                    v_a_6122_ = crate::leanh::lean_ctor_get(v___x_6121_, 0);
                    crate::leanh::lean_inc(v_a_6122_);
                    crate::leanh::lean_dec_ref_known(v___x_6121_, 1);
                    v___x_6123_ = l_Lean_Expr_mvarId_x21(v_a_6122_);
                    v___x_6124_ = l_Lean_MVarId_intros(
                        v___x_6123_,
                        v___y_6113_,
                        v___y_6114_,
                        v___y_6115_,
                        v___y_6116_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6124_) == 0 {
                        v_a_6125_ = crate::leanh::lean_ctor_get(v___x_6124_, 0);
                        crate::leanh::lean_inc(v_a_6125_);
                        crate::leanh::lean_dec_ref_known(v___x_6124_, 1);
                        v_snd_6126_ = crate::leanh::lean_ctor_get(v_a_6125_, 1);
                        crate::leanh::lean_inc_n(v_snd_6126_, 2);
                        crate::leanh::lean_dec(v_a_6125_);
                        v___x_6127_ = crate::leanh::lean_unsigned_to_nat(10);
                        v___x_6128_ = 0;
                        v___x_6129_ = crate::leanh::lean_box((v___x_6108_) as usize);
                        v___x_6130_ = crate::leanh::lean_box((v___x_6128_) as usize);
                        v___f_6131_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___boxed
                                as *mut core::ffi::c_void,
                            16,
                            9,
                        );
                        crate::leanh::lean_closure_set(v___f_6131_, 0, v_snd_6126_);
                        crate::leanh::lean_closure_set(v___f_6131_, 1, v___f_6106_);
                        crate::leanh::lean_closure_set(v___f_6131_, 2, v___f_6107_);
                        crate::leanh::lean_closure_set(v___f_6131_, 3, v___x_6127_);
                        crate::leanh::lean_closure_set(v___f_6131_, 4, v___x_6129_);
                        crate::leanh::lean_closure_set(v___f_6131_, 5, v___x_6130_);
                        crate::leanh::lean_closure_set(v___f_6131_, 6, v_expectedType_6110_);
                        crate::leanh::lean_closure_set(v___f_6131_, 7, v_a_6122_);
                        crate::leanh::lean_closure_set(v___f_6131_, 8, v_stx_6109_);
                        v___x_6132_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(v_snd_6126_, v___f_6131_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_);
                        return v___x_6132_;
                    } else {
                        crate::leanh::lean_dec(v_a_6122_);
                        crate::leanh::lean_dec_ref(v_expectedType_6110_);
                        crate::leanh::lean_dec(v_stx_6109_);
                        crate::leanh::lean_dec_ref(v___f_6107_);
                        crate::leanh::lean_dec_ref(v___f_6106_);
                        v_a_6133_ = crate::leanh::lean_ctor_get(v___x_6124_, 0);
                        v_isSharedCheck_6140_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6124_)) as u8;
                        if v_isSharedCheck_6140_ == 0 {
                            v___x_6135_ = v___x_6124_;
                            v_isShared_6136_ = v_isSharedCheck_6140_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6133_);
                            crate::leanh::lean_dec(v___x_6124_);
                            v___x_6135_ = crate::leanh::lean_box(0);
                            v_isShared_6136_ = v_isSharedCheck_6140_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_expectedType_6110_);
                    crate::leanh::lean_dec(v_stx_6109_);
                    crate::leanh::lean_dec_ref(v___f_6107_);
                    crate::leanh::lean_dec_ref(v___f_6106_);
                    return v___x_6121_;
                }
            }
            1 => {
                if v_isShared_6136_ == 0 {
                    v___x_6138_ = v___x_6135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6139_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_a_6133_);
                    v___x_6138_ = v_reuseFailAlloc_6139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__3___boxed(
    mut v___f_6141_: *mut crate::leanh::LeanObject,
    mut v___f_6142_: *mut crate::leanh::LeanObject,
    mut v___x_6143_: *mut crate::leanh::LeanObject,
    mut v_stx_6144_: *mut crate::leanh::LeanObject,
    mut v_expectedType_6145_: *mut crate::leanh::LeanObject,
    mut v___y_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
    mut v___y_6150_: *mut crate::leanh::LeanObject,
    mut v___y_6151_: *mut crate::leanh::LeanObject,
    mut v___y_6152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7237__boxed_6153_: u8 = 0;
    let mut v_res_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7237__boxed_6153_ = (crate::leanh::lean_unbox(v___x_6143_) as u8);
    v_res_6154_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__3(
        v___f_6141_,
        v___f_6142_,
        v___x_7237__boxed_6153_,
        v_stx_6144_,
        v_expectedType_6145_,
        v___y_6146_,
        v___y_6147_,
        v___y_6148_,
        v___y_6149_,
        v___y_6150_,
        v___y_6151_,
    );
    crate::leanh::lean_dec(v___y_6151_);
    crate::leanh::lean_dec_ref(v___y_6150_);
    crate::leanh::lean_dec(v___y_6149_);
    crate::leanh::lean_dec_ref(v___y_6148_);
    crate::leanh::lean_dec(v___y_6147_);
    crate::leanh::lean_dec_ref(v___y_6146_);
    return v_res_6154_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm(
    mut v_stx_6162_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_6163_: *mut crate::leanh::LeanObject,
    mut v_a_6164_: *mut crate::leanh::LeanObject,
    mut v_a_6165_: *mut crate::leanh::LeanObject,
    mut v_a_6166_: *mut crate::leanh::LeanObject,
    mut v_a_6167_: *mut crate::leanh::LeanObject,
    mut v_a_6168_: *mut crate::leanh::LeanObject,
    mut v_a_6169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: u8 = 0;
    v___x_6171_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1;
    crate::leanh::lean_inc(v_stx_6162_);
    v___x_6172_ = l_Lean_Syntax_isOfKind(v_stx_6162_, v___x_6171_);
    if v___x_6172_ == 0 {
        let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_expectedType_x3f_6163_);
        crate::leanh::lean_dec(v_stx_6162_);
        v___x_6173_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg();
        return v___x_6173_;
    } else {
        let mut v___f_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_6174_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2;
        v___x_6175_ = crate::leanh::lean_box((v___x_6172_) as usize);
        v___f_6176_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1___boxed as *mut core::ffi::c_void,
            7,
            1,
        );
        crate::leanh::lean_closure_set(v___f_6176_, 0, v___x_6175_);
        v___x_6177_ = crate::leanh::lean_box((v___x_6172_) as usize);
        v___f_6178_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__3___boxed as *mut core::ffi::c_void,
            12,
            4,
        );
        crate::leanh::lean_closure_set(v___f_6178_, 0, v___f_6174_);
        crate::leanh::lean_closure_set(v___f_6178_, 1, v___f_6176_);
        crate::leanh::lean_closure_set(v___f_6178_, 2, v___x_6177_);
        crate::leanh::lean_closure_set(v___f_6178_, 3, v_stx_6162_);
        v___x_6179_ = l_Lean_Elab_Term_withExpectedType(
            v_expectedType_x3f_6163_,
            v___f_6178_,
            v_a_6164_,
            v_a_6165_,
            v_a_6166_,
            v_a_6167_,
            v_a_6168_,
            v_a_6169_,
        );
        return v___x_6179_;
    }
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___boxed(
    mut v_stx_6180_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_6181_: *mut crate::leanh::LeanObject,
    mut v_a_6182_: *mut crate::leanh::LeanObject,
    mut v_a_6183_: *mut crate::leanh::LeanObject,
    mut v_a_6184_: *mut crate::leanh::LeanObject,
    mut v_a_6185_: *mut crate::leanh::LeanObject,
    mut v_a_6186_: *mut crate::leanh::LeanObject,
    mut v_a_6187_: *mut crate::leanh::LeanObject,
    mut v_a_6188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6189_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm(
        v_stx_6180_,
        v_expectedType_x3f_6181_,
        v_a_6182_,
        v_a_6183_,
        v_a_6184_,
        v_a_6185_,
        v_a_6186_,
        v_a_6187_,
    );
    crate::leanh::lean_dec(v_a_6187_);
    crate::leanh::lean_dec_ref(v_a_6186_);
    crate::leanh::lean_dec(v_a_6185_);
    crate::leanh::lean_dec_ref(v_a_6184_);
    crate::leanh::lean_dec(v_a_6183_);
    crate::leanh::lean_dec_ref(v_a_6182_);
    return v_res_6189_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3(
    mut v_ref_6190_: *mut crate::leanh::LeanObject,
    mut v_msgData_6191_: *mut crate::leanh::LeanObject,
    mut v_severity_6192_: u8,
    mut v_isSilent_6193_: u8,
    mut v___y_6194_: *mut crate::leanh::LeanObject,
    mut v___y_6195_: *mut crate::leanh::LeanObject,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
    mut v___y_6198_: *mut crate::leanh::LeanObject,
    mut v___y_6199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6201_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(v_ref_6190_, v_msgData_6191_, v_severity_6192_, v_isSilent_6193_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
    return v___x_6201_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___boxed(
    mut v_ref_6202_: *mut crate::leanh::LeanObject,
    mut v_msgData_6203_: *mut crate::leanh::LeanObject,
    mut v_severity_6204_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6205_: *mut crate::leanh::LeanObject,
    mut v___y_6206_: *mut crate::leanh::LeanObject,
    mut v___y_6207_: *mut crate::leanh::LeanObject,
    mut v___y_6208_: *mut crate::leanh::LeanObject,
    mut v___y_6209_: *mut crate::leanh::LeanObject,
    mut v___y_6210_: *mut crate::leanh::LeanObject,
    mut v___y_6211_: *mut crate::leanh::LeanObject,
    mut v___y_6212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6213_: u8 = 0;
    let mut v_isSilent_boxed_6214_: u8 = 0;
    let mut v_res_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6213_ = (crate::leanh::lean_unbox(v_severity_6204_) as u8);
    v_isSilent_boxed_6214_ = (crate::leanh::lean_unbox(v_isSilent_6205_) as u8);
    v_res_6215_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3(v_ref_6202_, v_msgData_6203_, v_severity_boxed_6213_, v_isSilent_boxed_6214_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
    crate::leanh::lean_dec(v___y_6211_);
    crate::leanh::lean_dec_ref(v___y_6210_);
    crate::leanh::lean_dec(v___y_6209_);
    crate::leanh::lean_dec_ref(v___y_6208_);
    crate::leanh::lean_dec(v___y_6207_);
    crate::leanh::lean_dec_ref(v___y_6206_);
    crate::leanh::lean_dec(v_ref_6202_);
    return v_res_6215_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6223_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6224_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1;
    v___x_6225_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1;
    v___x_6226_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6227_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6223_,
        v___x_6224_,
        v___x_6225_,
        v___x_6226_,
    );
    return v___x_6227_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___boxed(
    mut v_a_6228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6229_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1();
    return v_res_6229_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6256_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1;
    v___x_6257_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6;
    v___x_6258_ = l_Lean_addBuiltinDeclarationRanges(v___x_6256_, v___x_6257_);
    return v___x_6258_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___boxed(
    mut v_a_6259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6260_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3();
    return v_res_6260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_LibrarySearch(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ConfigEval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig = _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig();
    crate::leanh::lean_mark_persistent(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_LibrarySearch(
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
pub unsafe fn initialize_Lean_Elab_Tactic_LibrarySearch(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_ElabTerm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_ConfigEval(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
}
