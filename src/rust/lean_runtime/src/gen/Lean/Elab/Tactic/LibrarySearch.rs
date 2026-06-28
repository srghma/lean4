// Lean compiler output
// Module: Lean.Elab.Tactic.LibrarySearch
// Imports: Lean.Meta.Tactic.LibrarySearch Lean.Meta.Tactic.TryThis Lean.Elab.Tactic.ElabTerm Lean.Elab.ConfigEval
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7,
    lean_apply_9, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__0_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [102, 97, 105, 108, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [76, 105, 98, 114, 97, 114, 121, 83, 101, 97, 114, 99, 104, 67, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut LeanObject,9896841084116499507 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [10, 111, 102, 32, 116, 121, 112, 101, 32, 96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 116, 104, 101, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [69, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 99, 111, 110, 116, 97, 105, 110, 115, 32, 96, 115, 111, 114, 114, 121, 96, 58, 0]};
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 108, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 110, 102, 105, 103, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [103, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 97, 114, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 114, 121, 63, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut LeanObject,9896841084116499507 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__5_value) as *mut LeanObject,15737842007922976103 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut LeanObject,9896841084116499507 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__4_value) as *mut LeanObject,1745771790535957399 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__7_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut LeanObject,9896841084116499507 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__3_value) as *mut LeanObject,11983762874465944583 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__8_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__4_value) as *mut LeanObject,9896841084116499507 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__1_value) as *mut LeanObject,16400000088529102175 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
pub static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__5_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            97, 112, 112, 108, 121, 63, 32, 100, 105, 100, 110, 39, 116, 32, 102, 105, 110, 100,
            32, 97, 110, 121, 32, 114, 101, 108, 101, 118, 97, 110, 116, 32, 108, 101, 109, 109,
            97, 115, 0,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value: LeanStringObject<7> =
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
        m_data: [97, 112, 112, 108, 121, 63, 0],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value)
                as *mut LeanObject,
            5070879632462810678 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7_value: LeanStringObject<35> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            96, 101, 120, 97, 99, 116, 63, 96, 32, 99, 111, 117, 108, 100, 32, 110, 111, 116, 32,
            99, 108, 111, 115, 101, 32, 116, 104, 101, 32, 103, 111, 97, 108, 46, 0,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            32, 84, 114, 121, 32, 96, 97, 112, 112, 108, 121, 63, 96, 32, 116, 111, 32, 115, 101,
            101, 32, 112, 97, 114, 116, 105, 97, 108, 32, 115, 117, 103, 103, 101, 115, 116, 105,
            111, 110, 115, 46, 0,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_exact_x3f___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_LibrarySearch_exact_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__0_value: LeanStringObject<7> =
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
        m_data: [101, 120, 97, 99, 116, 63, 0],
    };
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__0_value) as *mut LeanObject;
static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__0_value)
                as *mut LeanObject,
            5826269145198601482 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__2_value: LeanStringObject<10> =
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
        m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0],
    };
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__2_value) as *mut LeanObject;
static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__2_value)
                as *mut LeanObject,
            3488656302031949961 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_evalExact___closed__4_value: LeanArrayObject<0> =
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
static mut l_Lean_Elab_LibrarySearch_evalExact___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [76, 105, 98, 114, 97, 114, 121, 83, 101, 97, 114, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 69, 120, 97, 99, 116, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut LeanObject,17680530212324118304 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__1_value) as *mut LeanObject,11860042555288360565 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 54 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__1_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut LeanObject,((( 13 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__4_value) as *mut LeanObject,((( 13 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6_value) as *mut LeanObject;
static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l_Lean_Elab_LibrarySearch_evalApply___closed__0_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__5_value)
                as *mut LeanObject,
            16444823490062833535 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_evalApply___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalApply___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 65, 112, 112, 108, 121, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut LeanObject,17680530212324118304 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__0_value) as *mut LeanObject,559802866465757943 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 61 as usize) << 1) | 1) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__1_value) as *mut LeanObject,((( 34 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut LeanObject,((( 13 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__4_value) as *mut LeanObject,((( 13 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0_value:
    LeanStringObject<80> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__0_value
    ) as *mut LeanObject],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3_value:
    LeanStringObject<42> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__3_value
    ) as *mut LeanObject],
};
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__6_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0_value: LeanStringObject<7> =
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
        m_data: [83, 121, 110, 116, 97, 120, 0],
    };
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__2_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__0_value)
                as *mut LeanObject,
            1765827125244227832 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_evalExact___closed__0_value)
                as *mut LeanObject,
            11838310352122951404 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 69, 120, 97, 99, 116, 63, 84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__0_value) as *mut LeanObject,17680530212324118304 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__0_value) as *mut LeanObject,1366678009817496993 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 76 as usize) << 1) | 1) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__1_value) as *mut LeanObject,((( 29 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 64 as usize) << 1) | 1) as *mut LeanObject,((( 18 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__3_value) as *mut LeanObject,((( 4 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__4_value) as *mut LeanObject,((( 18 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    v___x_3131_ = lean_box(0);
    v___x_3132_ = l_Lean_Elab_ConfigEval_unsupportedExprExceptionId;
    v___x_3133_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3133_, 0, v___x_3132_);
    lean_ctor_set(v___x_3133_, 1, v___x_3131_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    v___x_3135_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___closed__0);
    v___x_3136_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3136_, 0, v___x_3135_);
    return v___x_3136_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg___boxed(
    mut v___y_3137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3138_: *mut LeanObject = core::ptr::null_mut();
    v_res_3138_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg();
    return v_res_3138_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0(
    mut v_00_u03b1_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    v___x_3145_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___redArg();
    return v___x_3145_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0___boxed(
    mut v_00_u03b1_3146_: *mut LeanObject,
    mut v___y_3147_: *mut LeanObject,
    mut v___y_3148_: *mut LeanObject,
    mut v___y_3149_: *mut LeanObject,
    mut v___y_3150_: *mut LeanObject,
    mut v___y_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3152_: *mut LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Elab_ConfigEval_throwUnsupportedExpr___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__0(v_00_u03b1_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
    lean_dec(v___y_3150_);
    lean_dec_ref(v___y_3149_);
    lean_dec(v___y_3148_);
    lean_dec_ref(v___y_3147_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(
    mut v_msgData_3153_: *mut LeanObject,
    mut v___y_3154_: *mut LeanObject,
    mut v___y_3155_: *mut LeanObject,
    mut v___y_3156_: *mut LeanObject,
    mut v___y_3157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    v___x_3159_ = lean_st_ref_get(v___y_3157_);
    v_env_3160_ = lean_ctor_get(v___x_3159_, 0);
    lean_inc_ref(v_env_3160_);
    lean_dec(v___x_3159_);
    v___x_3161_ = lean_st_ref_get(v___y_3155_);
    v_mctx_3162_ = lean_ctor_get(v___x_3161_, 0);
    lean_inc_ref(v_mctx_3162_);
    lean_dec(v___x_3161_);
    v_lctx_3163_ = lean_ctor_get(v___y_3154_, 2);
    v_options_3164_ = lean_ctor_get(v___y_3156_, 2);
    lean_inc_ref(v_options_3164_);
    lean_inc_ref(v_lctx_3163_);
    v___x_3165_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3165_, 0, v_env_3160_);
    lean_ctor_set(v___x_3165_, 1, v_mctx_3162_);
    lean_ctor_set(v___x_3165_, 2, v_lctx_3163_);
    lean_ctor_set(v___x_3165_, 3, v_options_3164_);
    v___x_3166_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3166_, 0, v___x_3165_);
    lean_ctor_set(v___x_3166_, 1, v_msgData_3153_);
    v___x_3167_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3167_, 0, v___x_3166_);
    return v___x_3167_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1___boxed(
    mut v_msgData_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
    mut v___y_3171_: *mut LeanObject,
    mut v___y_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3174_: *mut LeanObject = core::ptr::null_mut();
    v_res_3174_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msgData_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
    lean_dec(v___y_3172_);
    lean_dec_ref(v___y_3171_);
    lean_dec(v___y_3170_);
    lean_dec_ref(v___y_3169_);
    return v_res_3174_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(
    mut v_msg_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3181_ = lean_ctor_get(v___y_3178_, 5);
                v___x_3182_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msg_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_);
                v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
                v_isSharedCheck_3191_ = (!lean_is_exclusive(v___x_3182_)) as u8;
                if v_isSharedCheck_3191_ == 0 {
                    v___x_3185_ = v___x_3182_;
                    v_isShared_3186_ = v_isSharedCheck_3191_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3183_);
                    lean_dec(v___x_3182_);
                    v___x_3185_ = lean_box(0);
                    v_isShared_3186_ = v_isSharedCheck_3191_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3181_);
                v___x_3187_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3187_, 0, v_ref_3181_);
                lean_ctor_set(v___x_3187_, 1, v_a_3183_);
                if v_isShared_3186_ == 0 {
                    lean_ctor_set_tag(v___x_3185_, 1);
                    lean_ctor_set(v___x_3185_, 0, v___x_3187_);
                    v___x_3189_ = v___x_3185_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
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
    mut v_msg_3192_: *mut LeanObject,
    mut v___y_3193_: *mut LeanObject,
    mut v___y_3194_: *mut LeanObject,
    mut v___y_3195_: *mut LeanObject,
    mut v___y_3196_: *mut LeanObject,
    mut v___y_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3198_: *mut LeanObject = core::ptr::null_mut();
    v_res_3198_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(v_msg_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
    lean_dec(v___y_3196_);
    lean_dec_ref(v___y_3195_);
    lean_dec(v___y_3194_);
    lean_dec_ref(v___y_3193_);
    return v_res_3198_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    v___x_3201_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__1;
    v___x_3202_ = l_Lean_stringToMessageData(v___x_3201_);
    return v___x_3202_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0(
    mut v_ctor_3203_: *mut LeanObject,
    mut v_args_3204_: *mut LeanObject,
    mut v___y_3205_: *mut LeanObject,
    mut v___y_3206_: *mut LeanObject,
    mut v___y_3207_: *mut LeanObject,
    mut v___y_3208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3230_: u8 = 0;
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: u8 = 0;
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: u8 = 0;
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3239_: u8 = 0;
    let mut v_a_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3247_: u8 = 0;
    let mut v_a_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3251_: u8 = 0;
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_a_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_a_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3267_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3271_: u8 = 0;
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: u8 = 0;
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3283_: u8 = 0;
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut LeanObject = core::ptr::null_mut();
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
                    v___x_3276_ = lean_unsigned_to_nat(4);
                    v___x_3277_ = lean_nat_dec_eq(v___x_3275_, v___x_3276_);
                    if v___x_3277_ == 0 {
                        v___x_3278_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0___closed__2);
                        v___x_3279_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(v___x_3278_, v___y_3205_, v___y_3206_, v___y_3207_, v___y_3208_);
                        v_a_3280_ = lean_ctor_get(v___x_3279_, 0);
                        v_isSharedCheck_3287_ = (!lean_is_exclusive(v___x_3279_)) as u8;
                        if v_isSharedCheck_3287_ == 0 {
                            v___x_3282_ = v___x_3279_;
                            v_isShared_3283_ = v_isSharedCheck_3287_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_3280_);
                            lean_dec(v___x_3279_);
                            v___x_3282_ = lean_box(0);
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
                v___x_3212_ = lean_unsigned_to_nat(0);
                v___x_3213_ = lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3212_);
                lean_inc(v___x_3213_);
                v___x_3214_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                    v___x_3213_,
                    v___y_3205_,
                    v___y_3206_,
                    v___y_3207_,
                    v___y_3208_,
                );
                if lean_obj_tag(v___x_3214_) == 0 {
                    v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
                    lean_inc(v_a_3215_);
                    lean_dec_ref_known(v___x_3214_, 1);
                    v___x_3216_ = lean_unsigned_to_nat(1);
                    v___x_3217_ = lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3216_);
                    lean_inc(v___x_3217_);
                    v___x_3218_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                        v___x_3217_,
                        v___y_3205_,
                        v___y_3206_,
                        v___y_3207_,
                        v___y_3208_,
                    );
                    if lean_obj_tag(v___x_3218_) == 0 {
                        v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
                        lean_inc(v_a_3219_);
                        lean_dec_ref_known(v___x_3218_, 1);
                        v___x_3220_ = lean_unsigned_to_nat(2);
                        v___x_3221_ =
                            lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3220_);
                        lean_inc(v___x_3221_);
                        v___x_3222_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                            v___x_3221_,
                            v___y_3205_,
                            v___y_3206_,
                            v___y_3207_,
                            v___y_3208_,
                        );
                        if lean_obj_tag(v___x_3222_) == 0 {
                            v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
                            lean_inc(v_a_3223_);
                            lean_dec_ref_known(v___x_3222_, 1);
                            v___x_3224_ = lean_unsigned_to_nat(3);
                            v___x_3225_ =
                                lean_array_get_borrowed(v___x_3211_, v_args_3204_, v___x_3224_);
                            lean_inc(v___x_3225_);
                            v___x_3226_ = l_Lean_Elab_ConfigEval_EvalExpr_evalBoolExpr(
                                v___x_3225_,
                                v___y_3205_,
                                v___y_3206_,
                                v___y_3207_,
                                v___y_3208_,
                            );
                            if lean_obj_tag(v___x_3226_) == 0 {
                                v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
                                v_isSharedCheck_3239_ = (!lean_is_exclusive(v___x_3226_)) as u8;
                                if v_isSharedCheck_3239_ == 0 {
                                    v___x_3229_ = v___x_3226_;
                                    v_isShared_3230_ = v_isSharedCheck_3239_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3227_);
                                    lean_dec(v___x_3226_);
                                    v___x_3229_ = lean_box(0);
                                    v_isShared_3230_ = v_isSharedCheck_3239_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3223_);
                                lean_dec(v_a_3219_);
                                lean_dec(v_a_3215_);
                                v_a_3240_ = lean_ctor_get(v___x_3226_, 0);
                                v_isSharedCheck_3247_ = (!lean_is_exclusive(v___x_3226_)) as u8;
                                if v_isSharedCheck_3247_ == 0 {
                                    v___x_3242_ = v___x_3226_;
                                    v_isShared_3243_ = v_isSharedCheck_3247_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_3240_);
                                    lean_dec(v___x_3226_);
                                    v___x_3242_ = lean_box(0);
                                    v_isShared_3243_ = v_isSharedCheck_3247_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3219_);
                            lean_dec(v_a_3215_);
                            v_a_3248_ = lean_ctor_get(v___x_3222_, 0);
                            v_isSharedCheck_3255_ = (!lean_is_exclusive(v___x_3222_)) as u8;
                            if v_isSharedCheck_3255_ == 0 {
                                v___x_3250_ = v___x_3222_;
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3248_);
                                lean_dec(v___x_3222_);
                                v___x_3250_ = lean_box(0);
                                v_isShared_3251_ = v_isSharedCheck_3255_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3215_);
                        v_a_3256_ = lean_ctor_get(v___x_3218_, 0);
                        v_isSharedCheck_3263_ = (!lean_is_exclusive(v___x_3218_)) as u8;
                        if v_isSharedCheck_3263_ == 0 {
                            v___x_3258_ = v___x_3218_;
                            v_isShared_3259_ = v_isSharedCheck_3263_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3256_);
                            lean_dec(v___x_3218_);
                            v___x_3258_ = lean_box(0);
                            v_isShared_3259_ = v_isSharedCheck_3263_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_3264_ = lean_ctor_get(v___x_3214_, 0);
                    v_isSharedCheck_3271_ = (!lean_is_exclusive(v___x_3214_)) as u8;
                    if v_isSharedCheck_3271_ == 0 {
                        v___x_3266_ = v___x_3214_;
                        v_isShared_3267_ = v_isSharedCheck_3271_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3264_);
                        lean_dec(v___x_3214_);
                        v___x_3266_ = lean_box(0);
                        v_isShared_3267_ = v_isSharedCheck_3271_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3231_ = lean_alloc_ctor(0, 0, (4) as u32);
                v___x_3232_ = (lean_unbox(v_a_3215_) as u8);
                lean_dec(v_a_3215_);
                lean_ctor_set_uint8(v___x_3231_, 0 as u32, v___x_3232_);
                v___x_3233_ = (lean_unbox(v_a_3219_) as u8);
                lean_dec(v_a_3219_);
                lean_ctor_set_uint8(v___x_3231_, 1 as u32, v___x_3233_);
                v___x_3234_ = (lean_unbox(v_a_3223_) as u8);
                lean_dec(v_a_3223_);
                lean_ctor_set_uint8(v___x_3231_, 2 as u32, v___x_3234_);
                v___x_3235_ = (lean_unbox(v_a_3227_) as u8);
                lean_dec(v_a_3227_);
                lean_ctor_set_uint8(v___x_3231_, 3 as u32, v___x_3235_);
                if v_isShared_3230_ == 0 {
                    lean_ctor_set(v___x_3229_, 0, v___x_3231_);
                    v___x_3237_ = v___x_3229_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3231_);
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
                    v_reuseFailAlloc_3246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_a_3240_);
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
                    v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
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
                    v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
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
                    v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
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
                    v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
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
    mut v_ctor_3288_: *mut LeanObject,
    mut v_args_3289_: *mut LeanObject,
    mut v___y_3290_: *mut LeanObject,
    mut v___y_3291_: *mut LeanObject,
    mut v___y_3292_: *mut LeanObject,
    mut v___y_3293_: *mut LeanObject,
    mut v___y_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3295_: *mut LeanObject = core::ptr::null_mut();
    v_res_3295_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___lam__0(v_ctor_3288_, v_args_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
    lean_dec(v___y_3293_);
    lean_dec_ref(v___y_3292_);
    lean_dec(v___y_3291_);
    lean_dec_ref(v___y_3290_);
    lean_dec_ref(v_args_3289_);
    lean_dec_ref(v_ctor_3288_);
    return v_res_3295_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr(
    mut v_a_3306_: *mut LeanObject,
    mut v_a_3307_: *mut LeanObject,
    mut v_a_3308_: *mut LeanObject,
    mut v_a_3309_: *mut LeanObject,
    mut v_a_3310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_a_3315_: *mut LeanObject,
    mut v_a_3316_: *mut LeanObject,
    mut v_a_3317_: *mut LeanObject,
    mut v_a_3318_: *mut LeanObject,
    mut v_a_3319_: *mut LeanObject,
    mut v_a_3320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3321_: *mut LeanObject = core::ptr::null_mut();
    v_res_3321_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr(v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_);
    lean_dec(v_a_3319_);
    lean_dec_ref(v_a_3318_);
    lean_dec(v_a_3317_);
    lean_dec_ref(v_a_3316_);
    return v_res_3321_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1(
    mut v_00_u03b1_3322_: *mut LeanObject,
    mut v_msg_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    v___x_3329_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___redArg(v_msg_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
    return v___x_3329_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1___boxed(
    mut v_00_u03b1_3330_: *mut LeanObject,
    mut v_msg_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
    mut v___y_3333_: *mut LeanObject,
    mut v___y_3334_: *mut LeanObject,
    mut v___y_3335_: *mut LeanObject,
    mut v___y_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3337_: *mut LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1(v_00_u03b1_3330_, v_msg_3331_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
    lean_dec(v___y_3335_);
    lean_dec_ref(v___y_3334_);
    lean_dec(v___y_3333_);
    lean_dec_ref(v___y_3332_);
    return v_res_3337_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1()
-> *mut LeanObject {
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    v___x_3339_ = lean_box(0);
    v___x_3340_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5;
    v___x_3341_ = l_Lean_Expr_const___override(v___x_3340_, v___x_3339_);
    return v___x_3341_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2()
-> *mut LeanObject {
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    v___x_3342_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1);
    v___x_3343_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3343_, 0, v___x_3342_);
    return v___x_3343_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3()
-> *mut LeanObject {
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v___x_3344_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2);
    v___x_3345_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__0;
    v___x_3346_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3346_, 0, v___x_3345_);
    lean_ctor_set(v___x_3346_, 1, v___x_3344_);
    return v___x_3346_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig()
-> *mut LeanObject {
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    v___x_3347_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__3);
    return v___x_3347_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(
    mut v_opts_3348_: *mut LeanObject,
    mut v_opt_3349_: *mut LeanObject,
) -> u8 {
    let mut v_name_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    v_name_3350_ = lean_ctor_get(v_opt_3349_, 0);
    v_defValue_3351_ = lean_ctor_get(v_opt_3349_, 1);
    v_map_3352_ = lean_ctor_get(v_opts_3348_, 0);
    v___x_3353_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3352_,
            v_name_3350_,
        );
    if lean_obj_tag(v___x_3353_) == 0 {
        let mut v___x_3354_: u8 = 0;
        v___x_3354_ = (lean_unbox(v_defValue_3351_) as u8);
        return v___x_3354_;
    } else {
        let mut v_val_3355_: *mut LeanObject = core::ptr::null_mut();
        v_val_3355_ = lean_ctor_get(v___x_3353_, 0);
        lean_inc(v_val_3355_);
        lean_dec_ref_known(v___x_3353_, 1);
        if lean_obj_tag(v_val_3355_) == 1 {
            let mut v_v_3356_: u8 = 0;
            v_v_3356_ = lean_ctor_get_uint8(v_val_3355_, 0 as u32);
            lean_dec_ref_known(v_val_3355_, 0);
            return v_v_3356_;
        } else {
            let mut v___x_3357_: u8 = 0;
            lean_dec(v_val_3355_);
            v___x_3357_ = (lean_unbox(v_defValue_3351_) as u8);
            return v___x_3357_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_opts_3358_: *mut LeanObject,
    mut v_opt_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3360_: u8 = 0;
    let mut v_r_3361_: *mut LeanObject = core::ptr::null_mut();
    v_res_3360_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_opts_3358_, v_opt_3359_);
    lean_dec_ref(v_opt_3359_);
    lean_dec_ref(v_opts_3358_);
    v_r_3361_ = lean_box((v_res_3360_) as usize);
    return v_r_3361_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0()
-> *mut LeanObject {
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    v___x_3362_ = lean_box(1);
    v___x_3363_ = l_Lean_MessageData_ofFormat(v___x_3362_);
    return v___x_3363_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    v___x_3367_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__2;
    v___x_3368_ = l_Lean_MessageData_ofFormat(v___x_3367_);
    return v___x_3368_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(
    mut v_x_3369_: *mut LeanObject,
    mut v_x_3370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3375_: u8 = 0;
    let mut v_before_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut v_unused_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3370_) == 0 {
                    return v_x_3369_;
                } else {
                    v_head_3371_ = lean_ctor_get(v_x_3370_, 0);
                    v_tail_3372_ = lean_ctor_get(v_x_3370_, 1);
                    v_isSharedCheck_3394_ = (!lean_is_exclusive(v_x_3370_)) as u8;
                    if v_isSharedCheck_3394_ == 0 {
                        v___x_3374_ = v_x_3370_;
                        v_isShared_3375_ = v_isSharedCheck_3394_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3372_);
                        lean_inc(v_head_3371_);
                        lean_dec(v_x_3370_);
                        v___x_3374_ = lean_box(0);
                        v_isShared_3375_ = v_isSharedCheck_3394_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3376_ = lean_ctor_get(v_head_3371_, 0);
                v_isSharedCheck_3392_ = (!lean_is_exclusive(v_head_3371_)) as u8;
                if v_isSharedCheck_3392_ == 0 {
                    v_unused_3393_ = lean_ctor_get(v_head_3371_, 1);
                    lean_dec(v_unused_3393_);
                    v___x_3378_ = v_head_3371_;
                    v_isShared_3379_ = v_isSharedCheck_3392_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_3376_);
                    lean_dec(v_head_3371_);
                    v___x_3378_ = lean_box(0);
                    v_isShared_3379_ = v_isSharedCheck_3392_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3380_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_3379_ == 0 {
                    lean_ctor_set_tag(v___x_3378_, 7);
                    lean_ctor_set(v___x_3378_, 1, v___x_3380_);
                    lean_ctor_set(v___x_3378_, 0, v_x_3369_);
                    v___x_3382_ = v___x_3378_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_x_3369_);
                    lean_ctor_set(v_reuseFailAlloc_3391_, 1, v___x_3380_);
                    v___x_3382_ = v_reuseFailAlloc_3391_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3383_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__3);
                if v_isShared_3375_ == 0 {
                    lean_ctor_set_tag(v___x_3374_, 7);
                    lean_ctor_set(v___x_3374_, 1, v___x_3383_);
                    lean_ctor_set(v___x_3374_, 0, v___x_3382_);
                    v___x_3385_ = v___x_3374_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 0, v___x_3382_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3383_);
                    v___x_3385_ = v_reuseFailAlloc_3390_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3386_ = l_Lean_MessageData_ofSyntax(v_before_3376_);
                v___x_3387_ = l_Lean_indentD(v___x_3386_);
                v___x_3388_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3388_, 0, v___x_3385_);
                lean_ctor_set(v___x_3388_, 1, v___x_3387_);
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
-> *mut LeanObject {
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    v___x_3398_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__1;
    v___x_3399_ = l_Lean_MessageData_ofFormat(v___x_3398_);
    return v___x_3399_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(
    mut v_msgData_3400_: *mut LeanObject,
    mut v_macroStack_3401_: *mut LeanObject,
    mut v___y_3402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: u8 = 0;
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut v_unused_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3404_ = lean_ctor_get(v___y_3402_, 2);
                v___x_3405_ = l_Lean_Elab_pp_macroStack;
                v___x_3406_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__4(v_options_3404_, v___x_3405_);
                if v___x_3406_ == 0 {
                    lean_dec(v_macroStack_3401_);
                    v___x_3407_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3407_, 0, v_msgData_3400_);
                    return v___x_3407_;
                } else {
                    if lean_obj_tag(v_macroStack_3401_) == 0 {
                        v___x_3408_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3408_, 0, v_msgData_3400_);
                        return v___x_3408_;
                    } else {
                        v_head_3409_ = lean_ctor_get(v_macroStack_3401_, 0);
                        lean_inc(v_head_3409_);
                        v_after_3410_ = lean_ctor_get(v_head_3409_, 1);
                        v_isSharedCheck_3425_ = (!lean_is_exclusive(v_head_3409_)) as u8;
                        if v_isSharedCheck_3425_ == 0 {
                            v_unused_3426_ = lean_ctor_get(v_head_3409_, 0);
                            lean_dec(v_unused_3426_);
                            v___x_3412_ = v_head_3409_;
                            v_isShared_3413_ = v_isSharedCheck_3425_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_3410_);
                            lean_dec(v_head_3409_);
                            v___x_3412_ = lean_box(0);
                            v_isShared_3413_ = v_isSharedCheck_3425_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3414_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5___closed__0);
                if v_isShared_3413_ == 0 {
                    lean_ctor_set_tag(v___x_3412_, 7);
                    lean_ctor_set(v___x_3412_, 1, v___x_3414_);
                    lean_ctor_set(v___x_3412_, 0, v_msgData_3400_);
                    v___x_3416_ = v___x_3412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3424_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_msgData_3400_);
                    lean_ctor_set(v_reuseFailAlloc_3424_, 1, v___x_3414_);
                    v___x_3416_ = v_reuseFailAlloc_3424_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3417_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___closed__2);
                v___x_3418_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3418_, 0, v___x_3416_);
                lean_ctor_set(v___x_3418_, 1, v___x_3417_);
                v___x_3419_ = l_Lean_MessageData_ofSyntax(v_after_3410_);
                v___x_3420_ = l_Lean_indentD(v___x_3419_);
                v_msgData_3421_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_3421_, 0, v___x_3418_);
                lean_ctor_set(v_msgData_3421_, 1, v___x_3420_);
                v___x_3422_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2_spec__5(v_msgData_3421_, v_macroStack_3401_);
                v___x_3423_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3423_, 0, v___x_3422_);
                return v___x_3423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_msgData_3427_: *mut LeanObject,
    mut v_macroStack_3428_: *mut LeanObject,
    mut v___y_3429_: *mut LeanObject,
    mut v___y_3430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3431_: *mut LeanObject = core::ptr::null_mut();
    v_res_3431_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3427_, v_macroStack_3428_, v___y_3429_);
    lean_dec_ref(v___y_3429_);
    return v_res_3431_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(
    mut v_msg_3432_: *mut LeanObject,
    mut v___y_3433_: *mut LeanObject,
    mut v___y_3434_: *mut LeanObject,
    mut v___y_3435_: *mut LeanObject,
    mut v___y_3436_: *mut LeanObject,
    mut v___y_3437_: *mut LeanObject,
    mut v___y_3438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3440_ = lean_ctor_get(v___y_3437_, 5);
                v___x_3441_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msg_3432_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_);
                v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
                lean_inc(v_a_3442_);
                lean_dec_ref(v___x_3441_);
                v_macroStack_3443_ = lean_ctor_get(v___y_3433_, 1);
                v___x_3444_ = l_Lean_Elab_getBetterRef(v_ref_3440_, v_macroStack_3443_);
                lean_inc(v_macroStack_3443_);
                v___x_3445_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_a_3442_, v_macroStack_3443_, v___y_3437_);
                v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
                v_isSharedCheck_3454_ = (!lean_is_exclusive(v___x_3445_)) as u8;
                if v_isSharedCheck_3454_ == 0 {
                    v___x_3448_ = v___x_3445_;
                    v_isShared_3449_ = v_isSharedCheck_3454_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3446_);
                    lean_dec(v___x_3445_);
                    v___x_3448_ = lean_box(0);
                    v_isShared_3449_ = v_isSharedCheck_3454_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3450_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3450_, 0, v___x_3444_);
                lean_ctor_set(v___x_3450_, 1, v_a_3446_);
                if v_isShared_3449_ == 0 {
                    lean_ctor_set_tag(v___x_3448_, 1);
                    lean_ctor_set(v___x_3448_, 0, v___x_3450_);
                    v___x_3452_ = v___x_3448_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3450_);
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
    mut v_msg_3455_: *mut LeanObject,
    mut v___y_3456_: *mut LeanObject,
    mut v___y_3457_: *mut LeanObject,
    mut v___y_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3463_: *mut LeanObject = core::ptr::null_mut();
    v_res_3463_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_, v___y_3461_);
    lean_dec(v___y_3461_);
    lean_dec_ref(v___y_3460_);
    lean_dec(v___y_3459_);
    lean_dec_ref(v___y_3458_);
    lean_dec(v___y_3457_);
    lean_dec_ref(v___y_3456_);
    return v_res_3463_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(
    mut v_e_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3467_: u8 = 0;
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3487_: u8 = 0;
    let mut v_unused_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3467_ = l_Lean_Expr_hasMVar(v_e_3464_);
                if v___x_3467_ == 0 {
                    v___x_3468_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3468_, 0, v_e_3464_);
                    return v___x_3468_;
                } else {
                    v___x_3469_ = lean_st_ref_get(v___y_3465_);
                    v_mctx_3470_ = lean_ctor_get(v___x_3469_, 0);
                    lean_inc_ref(v_mctx_3470_);
                    lean_dec(v___x_3469_);
                    v___x_3471_ = l_Lean_instantiateMVarsCore(v_mctx_3470_, v_e_3464_);
                    v_fst_3472_ = lean_ctor_get(v___x_3471_, 0);
                    lean_inc(v_fst_3472_);
                    v_snd_3473_ = lean_ctor_get(v___x_3471_, 1);
                    lean_inc(v_snd_3473_);
                    lean_dec_ref(v___x_3471_);
                    v___x_3474_ = lean_st_ref_take(v___y_3465_);
                    v_cache_3475_ = lean_ctor_get(v___x_3474_, 1);
                    v_zetaDeltaFVarIds_3476_ = lean_ctor_get(v___x_3474_, 2);
                    v_postponed_3477_ = lean_ctor_get(v___x_3474_, 3);
                    v_diag_3478_ = lean_ctor_get(v___x_3474_, 4);
                    v_isSharedCheck_3487_ = (!lean_is_exclusive(v___x_3474_)) as u8;
                    if v_isSharedCheck_3487_ == 0 {
                        v_unused_3488_ = lean_ctor_get(v___x_3474_, 0);
                        lean_dec(v_unused_3488_);
                        v___x_3480_ = v___x_3474_;
                        v_isShared_3481_ = v_isSharedCheck_3487_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_3478_);
                        lean_inc(v_postponed_3477_);
                        lean_inc(v_zetaDeltaFVarIds_3476_);
                        lean_inc(v_cache_3475_);
                        lean_dec(v___x_3474_);
                        v___x_3480_ = lean_box(0);
                        v_isShared_3481_ = v_isSharedCheck_3487_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3481_ == 0 {
                    lean_ctor_set(v___x_3480_, 0, v_snd_3473_);
                    v___x_3483_ = v___x_3480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_snd_3473_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 1, v_cache_3475_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 2, v_zetaDeltaFVarIds_3476_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 3, v_postponed_3477_);
                    lean_ctor_set(v_reuseFailAlloc_3486_, 4, v_diag_3478_);
                    v___x_3483_ = v_reuseFailAlloc_3486_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3484_ = lean_st_ref_set(v___y_3465_, v___x_3483_);
                v___x_3485_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3485_, 0, v_fst_3472_);
                return v___x_3485_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg___boxed(
    mut v_e_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
    mut v___y_3491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3492_: *mut LeanObject = core::ptr::null_mut();
    v_res_3492_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3489_, v___y_3490_);
    lean_dec(v___y_3490_);
    return v_res_3492_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    v___x_3493_ = lean_box(0);
    v___x_3494_ = l_Lean_Elab_abortTermExceptionId;
    v___x_3495_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3495_, 0, v___x_3494_);
    lean_ctor_set(v___x_3495_, 1, v___x_3493_);
    return v___x_3495_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg()
-> *mut LeanObject {
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    v___x_3497_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___closed__0);
    v___x_3498_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3498_, 0, v___x_3497_);
    return v___x_3498_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg___boxed(
    mut v___y_3499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3500_: *mut LeanObject = core::ptr::null_mut();
    v_res_3500_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v_res_3500_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    v___x_3502_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__0;
    v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
    return v___x_3503_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2()
-> *mut LeanObject {
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    v___x_3504_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__1);
    v___x_3505_ = l_Lean_MessageData_ofExpr(v___x_3504_);
    return v___x_3505_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3()
-> *mut LeanObject {
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    v___x_3506_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__2);
    v___x_3507_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__1);
    v___x_3508_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3508_, 0, v___x_3507_);
    lean_ctor_set(v___x_3508_, 1, v___x_3506_);
    return v___x_3508_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5()
-> *mut LeanObject {
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    v___x_3510_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__4;
    v___x_3511_ = l_Lean_stringToMessageData(v___x_3510_);
    return v___x_3511_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6()
-> *mut LeanObject {
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    v___x_3512_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__5);
    v___x_3513_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__3);
    v___x_3514_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3514_, 0, v___x_3513_);
    lean_ctor_set(v___x_3514_, 1, v___x_3512_);
    return v___x_3514_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8()
-> *mut LeanObject {
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut LeanObject = core::ptr::null_mut();
    v___x_3516_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__7;
    v___x_3517_ = l_Lean_stringToMessageData(v___x_3516_);
    return v___x_3517_;
}
pub unsafe fn _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10()
-> *mut LeanObject {
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    v___x_3519_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__9;
    v___x_3520_ = l_Lean_stringToMessageData(v___x_3519_);
    return v___x_3520_;
}
pub unsafe fn l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0(
    mut v_stx_3521_: *mut LeanObject,
    mut v_a_3522_: *mut LeanObject,
    mut v_a_3523_: *mut LeanObject,
    mut v_a_3524_: *mut LeanObject,
    mut v_a_3525_: *mut LeanObject,
    mut v_a_3526_: *mut LeanObject,
    mut v_a_3527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ty_x3f_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3547_: u8 = 0;
    let mut v_cancelTk_x3f_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3549_: u8 = 0;
    let mut v_inheritedTraceOptions_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: u8 = 0;
    let mut v_ref_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: u8 = 0;
    let mut v_id_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3572_: u8 = 0;
    let mut v___x_3573_: u8 = 0;
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3582_: u8 = 0;
    let mut v_unused_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: u8 = 0;
    let mut v___y_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: u8 = 0;
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3612_: u8 = 0;
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3616_: u8 = 0;
    let mut v_a_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3624_: u8 = 0;
    let mut v_a_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3628_: u8 = 0;
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3632_: u8 = 0;
    let mut v___y_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3651_: u8 = 0;
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: u8 = 0;
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3658_: u8 = 0;
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3662_: u8 = 0;
    let mut v_a_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ty_x3f_3529_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2_once), _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig___closed__2);
                v___x_3530_ = 1;
                v___x_3531_ = lean_box(0);
                v___x_3532_ = lean_box((v___x_3530_) as usize);
                v___x_3533_ = lean_box((v___x_3530_) as usize);
                lean_inc(v_stx_3521_);
                v___x_3534_ = lean_alloc_closure(
                    l_Lean_Elab_Term_elabTermEnsuringType___boxed as *mut core::ffi::c_void,
                    12,
                    5,
                );
                lean_closure_set(v___x_3534_, 0, v_stx_3521_);
                lean_closure_set(v___x_3534_, 1, v_ty_x3f_3529_);
                lean_closure_set(v___x_3534_, 2, v___x_3532_);
                lean_closure_set(v___x_3534_, 3, v___x_3533_);
                lean_closure_set(v___x_3534_, 4, v___x_3531_);
                v_fileName_3535_ = lean_ctor_get(v_a_3526_, 0);
                v_fileMap_3536_ = lean_ctor_get(v_a_3526_, 1);
                v_options_3537_ = lean_ctor_get(v_a_3526_, 2);
                v_currRecDepth_3538_ = lean_ctor_get(v_a_3526_, 3);
                v_maxRecDepth_3539_ = lean_ctor_get(v_a_3526_, 4);
                v_ref_3540_ = lean_ctor_get(v_a_3526_, 5);
                v_currNamespace_3541_ = lean_ctor_get(v_a_3526_, 6);
                v_openDecls_3542_ = lean_ctor_get(v_a_3526_, 7);
                v_initHeartbeats_3543_ = lean_ctor_get(v_a_3526_, 8);
                v_maxHeartbeats_3544_ = lean_ctor_get(v_a_3526_, 9);
                v_quotContext_3545_ = lean_ctor_get(v_a_3526_, 10);
                v_currMacroScope_3546_ = lean_ctor_get(v_a_3526_, 11);
                v_diag_3547_ = lean_ctor_get_uint8(
                    v_a_3526_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_3548_ = lean_ctor_get(v_a_3526_, 12);
                v_suppressElabErrors_3549_ = lean_ctor_get_uint8(
                    v_a_3526_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_3550_ = lean_ctor_get(v_a_3526_, 13);
                v___x_3551_ = 1;
                v_ref_3552_ = l_Lean_replaceRef(v_stx_3521_, v_ref_3540_);
                lean_dec(v_stx_3521_);
                lean_inc_ref(v_inheritedTraceOptions_3550_);
                lean_inc(v_cancelTk_x3f_3548_);
                lean_inc(v_currMacroScope_3546_);
                lean_inc(v_quotContext_3545_);
                lean_inc(v_maxHeartbeats_3544_);
                lean_inc(v_initHeartbeats_3543_);
                lean_inc(v_openDecls_3542_);
                lean_inc(v_currNamespace_3541_);
                lean_inc(v_maxRecDepth_3539_);
                lean_inc(v_currRecDepth_3538_);
                lean_inc_ref(v_options_3537_);
                lean_inc_ref(v_fileMap_3536_);
                lean_inc_ref(v_fileName_3535_);
                v___x_3553_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_3553_, 0, v_fileName_3535_);
                lean_ctor_set(v___x_3553_, 1, v_fileMap_3536_);
                lean_ctor_set(v___x_3553_, 2, v_options_3537_);
                lean_ctor_set(v___x_3553_, 3, v_currRecDepth_3538_);
                lean_ctor_set(v___x_3553_, 4, v_maxRecDepth_3539_);
                lean_ctor_set(v___x_3553_, 5, v_ref_3552_);
                lean_ctor_set(v___x_3553_, 6, v_currNamespace_3541_);
                lean_ctor_set(v___x_3553_, 7, v_openDecls_3542_);
                lean_ctor_set(v___x_3553_, 8, v_initHeartbeats_3543_);
                lean_ctor_set(v___x_3553_, 9, v_maxHeartbeats_3544_);
                lean_ctor_set(v___x_3553_, 10, v_quotContext_3545_);
                lean_ctor_set(v___x_3553_, 11, v_currMacroScope_3546_);
                lean_ctor_set(v___x_3553_, 12, v_cancelTk_x3f_3548_);
                lean_ctor_set(v___x_3553_, 13, v_inheritedTraceOptions_3550_);
                lean_ctor_set_uint8(
                    v___x_3553_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_3547_,
                );
                lean_ctor_set_uint8(
                    v___x_3553_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_3549_,
                );
                v___x_3554_ =
                    l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp(
                        lean_box(0),
                        v___x_3534_,
                        v___x_3551_,
                        v_a_3522_,
                        v_a_3523_,
                        v_a_3524_,
                        v_a_3525_,
                        v___x_3553_,
                        v_a_3527_,
                    );
                if lean_obj_tag(v___x_3554_) == 0 {
                    v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
                    lean_inc(v_a_3555_);
                    lean_dec_ref_known(v___x_3554_, 1);
                    v___x_3556_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_3555_, v_a_3525_);
                    v_a_3557_ = lean_ctor_get(v___x_3556_, 0);
                    lean_inc(v_a_3557_);
                    lean_dec_ref(v___x_3556_);
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
                            lean_dec(v_a_3557_);
                            lean_dec_ref_known(v___x_3553_, 14);
                            v___x_3654_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_3655_ = lean_ctor_get(v___x_3654_, 0);
                            v_isSharedCheck_3662_ = (!lean_is_exclusive(v___x_3654_)) as u8;
                            if v_isSharedCheck_3662_ == 0 {
                                v___x_3657_ = v___x_3654_;
                                v_isShared_3658_ = v_isSharedCheck_3662_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_3655_);
                                lean_dec(v___x_3654_);
                                v___x_3657_ = lean_box(0);
                                v_isShared_3658_ = v_isSharedCheck_3662_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_3553_, 14);
                    v_a_3663_ = lean_ctor_get(v___x_3554_, 0);
                    v_isSharedCheck_3670_ = (!lean_is_exclusive(v___x_3554_)) as u8;
                    if v_isSharedCheck_3670_ == 0 {
                        v___x_3665_ = v___x_3554_;
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3663_);
                        lean_dec(v___x_3554_);
                        v___x_3665_ = lean_box(0);
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_3568_ == 0 {
                    if lean_obj_tag(v___y_3560_) == 0 {
                        lean_dec_ref_known(v___y_3560_, 2);
                        lean_dec_ref(v___y_3561_);
                        lean_dec(v_a_3557_);
                        return v___y_3564_;
                    } else {
                        v_id_3569_ = lean_ctor_get(v___y_3560_, 0);
                        v_isSharedCheck_3582_ = (!lean_is_exclusive(v___y_3560_)) as u8;
                        if v_isSharedCheck_3582_ == 0 {
                            v_unused_3583_ = lean_ctor_get(v___y_3560_, 1);
                            lean_dec(v_unused_3583_);
                            v___x_3571_ = v___y_3560_;
                            v_isShared_3572_ = v_isSharedCheck_3582_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_id_3569_);
                            lean_dec(v___y_3560_);
                            v___x_3571_ = lean_box(0);
                            v_isShared_3572_ = v_isSharedCheck_3582_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3561_);
                    lean_dec_ref(v___y_3560_);
                    lean_dec(v_a_3557_);
                    return v___y_3564_;
                }
            }
            2 => {
                v___x_3573_ = l_Lean_instBEqInternalExceptionId_beq(v___y_3565_, v_id_3569_);
                lean_dec(v_id_3569_);
                if v___x_3573_ == 0 {
                    lean_del_object(v___x_3571_);
                    lean_dec_ref(v___y_3561_);
                    lean_dec(v_a_3557_);
                    return v___y_3564_;
                } else {
                    lean_dec_ref(v___y_3564_);
                    v___x_3574_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__6);
                    v___x_3575_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__8);
                    v___x_3576_ = l_Lean_indentExpr(v_a_3557_);
                    if v_isShared_3572_ == 0 {
                        lean_ctor_set_tag(v___x_3571_, 7);
                        lean_ctor_set(v___x_3571_, 1, v___x_3576_);
                        lean_ctor_set(v___x_3571_, 0, v___x_3575_);
                        v___x_3578_ = v___x_3571_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3581_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3575_);
                        lean_ctor_set(v_reuseFailAlloc_3581_, 1, v___x_3576_);
                        v___x_3578_ = v_reuseFailAlloc_3581_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3579_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                lean_ctor_set(v___x_3579_, 1, v___x_3574_);
                v___x_3580_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3579_, v___y_3559_, v___y_3567_, v___y_3563_, v___y_3566_, v___y_3561_, v___y_3562_);
                lean_dec_ref(v___y_3561_);
                return v___x_3580_;
            }
            4 => {
                lean_inc(v_a_3557_);
                v___x_3591_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr(v_a_3557_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
                if lean_obj_tag(v___x_3591_) == 0 {
                    lean_dec_ref(v___y_3589_);
                    lean_dec(v_a_3557_);
                    return v___x_3591_;
                } else {
                    v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
                    lean_inc(v_a_3592_);
                    v___x_3593_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                    v___x_3594_ = l_Lean_Exception_isInterrupt(v_a_3592_);
                    if v___x_3594_ == 0 {
                        lean_inc(v_a_3592_);
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
                lean_inc(v_a_3557_);
                v___x_3603_ = l_Lean_Meta_getMVars(
                    v_a_3557_,
                    v___y_3599_,
                    v___y_3600_,
                    v___y_3601_,
                    v___y_3602_,
                );
                if lean_obj_tag(v___x_3603_) == 0 {
                    v_a_3604_ = lean_ctor_get(v___x_3603_, 0);
                    lean_inc(v_a_3604_);
                    lean_dec_ref_known(v___x_3603_, 1);
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
                    lean_dec(v_a_3604_);
                    if lean_obj_tag(v___x_3605_) == 0 {
                        v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
                        lean_inc(v_a_3606_);
                        lean_dec_ref_known(v___x_3605_, 1);
                        v___x_3607_ = (lean_unbox(v_a_3606_) as u8);
                        lean_dec(v_a_3606_);
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
                            lean_dec_ref(v___y_3601_);
                            lean_dec(v_a_3557_);
                            v___x_3608_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
                            v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
                            v_isSharedCheck_3616_ = (!lean_is_exclusive(v___x_3608_)) as u8;
                            if v_isSharedCheck_3616_ == 0 {
                                v___x_3611_ = v___x_3608_;
                                v_isShared_3612_ = v_isSharedCheck_3616_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3609_);
                                lean_dec(v___x_3608_);
                                v___x_3611_ = lean_box(0);
                                v_isShared_3612_ = v_isSharedCheck_3616_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_3601_);
                        lean_dec(v_a_3557_);
                        v_a_3617_ = lean_ctor_get(v___x_3605_, 0);
                        v_isSharedCheck_3624_ = (!lean_is_exclusive(v___x_3605_)) as u8;
                        if v_isSharedCheck_3624_ == 0 {
                            v___x_3619_ = v___x_3605_;
                            v_isShared_3620_ = v_isSharedCheck_3624_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_3617_);
                            lean_dec(v___x_3605_);
                            v___x_3619_ = lean_box(0);
                            v_isShared_3620_ = v_isSharedCheck_3624_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_3601_);
                    lean_dec(v_a_3557_);
                    v_a_3625_ = lean_ctor_get(v___x_3603_, 0);
                    v_isSharedCheck_3632_ = (!lean_is_exclusive(v___x_3603_)) as u8;
                    if v_isSharedCheck_3632_ == 0 {
                        v___x_3627_ = v___x_3603_;
                        v_isShared_3628_ = v_isSharedCheck_3632_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_3625_);
                        lean_dec(v___x_3603_);
                        v___x_3627_ = lean_box(0);
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
                    v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
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
                    v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
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
                    v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
                    v___x_3630_ = v_reuseFailAlloc_3631_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3630_;
            }
            12 => {
                v___x_3640_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10), core::ptr::addr_of_mut!(l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10_once), _init_l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0___closed__10);
                v___x_3641_ = l_Lean_indentExpr(v_a_3557_);
                v___x_3642_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_3642_, 0, v___x_3640_);
                lean_ctor_set(v___x_3642_, 1, v___x_3641_);
                v___x_3643_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v___x_3642_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
                lean_dec_ref(v___y_3638_);
                v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
                v_isSharedCheck_3651_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                if v_isSharedCheck_3651_ == 0 {
                    v___x_3646_ = v___x_3643_;
                    v_isShared_3647_ = v_isSharedCheck_3651_;
                    state = 13;
                    continue;
                } else {
                    lean_inc(v_a_3644_);
                    lean_dec(v___x_3643_);
                    v___x_3646_ = lean_box(0);
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
                    v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
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
                    v_reuseFailAlloc_3661_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3661_, 0, v_a_3655_);
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
                    v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
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
    mut v_stx_3671_: *mut LeanObject,
    mut v_a_3672_: *mut LeanObject,
    mut v_a_3673_: *mut LeanObject,
    mut v_a_3674_: *mut LeanObject,
    mut v_a_3675_: *mut LeanObject,
    mut v_a_3676_: *mut LeanObject,
    mut v_a_3677_: *mut LeanObject,
    mut v_a_3678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3679_: *mut LeanObject = core::ptr::null_mut();
    v_res_3679_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0(v_stx_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
    lean_dec(v_a_3677_);
    lean_dec_ref(v_a_3676_);
    lean_dec(v_a_3675_);
    lean_dec_ref(v_a_3674_);
    lean_dec(v_a_3673_);
    lean_dec_ref(v_a_3672_);
    return v_res_3679_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0(
    mut v_config_3711_: *mut LeanObject,
    mut v_item_3712_: *mut LeanObject,
    mut v___y_3713_: *mut LeanObject,
    mut v___y_3714_: *mut LeanObject,
    mut v___y_3715_: *mut LeanObject,
    mut v___y_3716_: *mut LeanObject,
    mut v___y_3717_: *mut LeanObject,
    mut v___y_3718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_item_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: u8 = 0;
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: u8 = 0;
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: u8 = 0;
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3752_: u8 = 0;
    let mut v_grind_3753_: u8 = 0;
    let mut v_star_3754_: u8 = 0;
    let mut v_all_3755_: u8 = 0;
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3758_: u8 = 0;
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: u8 = 0;
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_isSharedCheck_3767_: u8 = 0;
    let mut v_a_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3771_: u8 = 0;
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3775_: u8 = 0;
    let mut v_a_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3779_: u8 = 0;
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3783_: u8 = 0;
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v_grind_3792_: u8 = 0;
    let mut v_try_x3f_3793_: u8 = 0;
    let mut v_all_3794_: u8 = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3797_: u8 = 0;
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3805_: u8 = 0;
    let mut v_isSharedCheck_3806_: u8 = 0;
    let mut v_a_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3814_: u8 = 0;
    let mut v_a_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: u8 = 0;
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_try_x3f_3831_: u8 = 0;
    let mut v_star_3832_: u8 = 0;
    let mut v_all_3833_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v_isSharedCheck_3845_: u8 = 0;
    let mut v_a_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3849_: u8 = 0;
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3853_: u8 = 0;
    let mut v_a_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3861_: u8 = 0;
    let mut v___x_3862_: u8 = 0;
    let mut v_value_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v_grind_3873_: u8 = 0;
    let mut v_try_x3f_3874_: u8 = 0;
    let mut v_star_3875_: u8 = 0;
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3886_: u8 = 0;
    let mut v_isSharedCheck_3887_: u8 = 0;
    let mut v_a_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3895_: u8 = 0;
    let mut v_a_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3899_: u8 = 0;
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_a_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3907_: u8 = 0;
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3910_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_3731_) == 0 {
                    lean_dec_ref_known(v___x_3731_, 1);
                    v___x_3732_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v_item_3712_);
                    if v___x_3732_ == 0 {
                        v___x_3733_ = l_Lean_Elab_ConfigEval_ConfigItem_getRootStr(v_item_3712_);
                        lean_inc_ref(v_item_3712_);
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
                                        lean_dec_ref(v___x_3733_);
                                        if v___x_3744_ == 0 {
                                            lean_dec_ref(v_item_3712_);
                                            lean_dec_ref(v_config_3711_);
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
                                            if lean_obj_tag(v___x_3746_) == 0 {
                                                lean_dec_ref_known(v___x_3746_, 1);
                                                v___x_3747_ =
                                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                        v___x_3734_,
                                                    );
                                                if v___x_3747_ == 0 {
                                                    lean_dec_ref(v_item_3712_);
                                                    lean_dec_ref(v_config_3711_);
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
                                                    lean_dec_ref(v___x_3734_);
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
                                                    if lean_obj_tag(v___x_3748_) == 0 {
                                                        v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
                                                        v_isSharedCheck_3767_ =
                                                            (!lean_is_exclusive(v___x_3748_)) as u8;
                                                        if v_isSharedCheck_3767_ == 0 {
                                                            v___x_3751_ = v___x_3748_;
                                                            v_isShared_3752_ =
                                                                v_isSharedCheck_3767_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3749_);
                                                            lean_dec(v___x_3748_);
                                                            v___x_3751_ = lean_box(0);
                                                            v_isShared_3752_ =
                                                                v_isSharedCheck_3767_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_config_3711_);
                                                        v_a_3768_ = lean_ctor_get(v___x_3748_, 0);
                                                        v_isSharedCheck_3775_ =
                                                            (!lean_is_exclusive(v___x_3748_)) as u8;
                                                        if v_isSharedCheck_3775_ == 0 {
                                                            v___x_3770_ = v___x_3748_;
                                                            v_isShared_3771_ =
                                                                v_isSharedCheck_3775_;
                                                            state = 6;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_3768_);
                                                            lean_dec(v___x_3748_);
                                                            v___x_3770_ = lean_box(0);
                                                            v_isShared_3771_ =
                                                                v_isSharedCheck_3775_;
                                                            state = 6;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_3734_);
                                                lean_dec_ref(v_item_3712_);
                                                lean_dec_ref(v_config_3711_);
                                                v_a_3776_ = lean_ctor_get(v___x_3746_, 0);
                                                v_isSharedCheck_3783_ =
                                                    (!lean_is_exclusive(v___x_3746_)) as u8;
                                                if v_isSharedCheck_3783_ == 0 {
                                                    v___x_3778_ = v___x_3746_;
                                                    v_isShared_3779_ = v_isSharedCheck_3783_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3776_);
                                                    lean_dec(v___x_3746_);
                                                    v___x_3778_ = lean_box(0);
                                                    v_isShared_3779_ = v_isSharedCheck_3783_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_3733_);
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
                                        if lean_obj_tag(v___x_3785_) == 0 {
                                            lean_dec_ref_known(v___x_3785_, 1);
                                            v___x_3786_ =
                                                l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                                    v___x_3734_,
                                                );
                                            if v___x_3786_ == 0 {
                                                lean_dec_ref(v_item_3712_);
                                                lean_dec_ref(v_config_3711_);
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
                                                lean_dec_ref(v___x_3734_);
                                                v___x_3787_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                    v_item_3712_,
                                                    v___y_3713_,
                                                    v___y_3714_,
                                                    v___y_3715_,
                                                    v___y_3716_,
                                                    v___y_3717_,
                                                    v___y_3718_,
                                                );
                                                if lean_obj_tag(v___x_3787_) == 0 {
                                                    v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
                                                    v_isSharedCheck_3806_ =
                                                        (!lean_is_exclusive(v___x_3787_)) as u8;
                                                    if v_isSharedCheck_3806_ == 0 {
                                                        v___x_3790_ = v___x_3787_;
                                                        v_isShared_3791_ = v_isSharedCheck_3806_;
                                                        state = 10;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3788_);
                                                        lean_dec(v___x_3787_);
                                                        v___x_3790_ = lean_box(0);
                                                        v_isShared_3791_ = v_isSharedCheck_3806_;
                                                        state = 10;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_config_3711_);
                                                    v_a_3807_ = lean_ctor_get(v___x_3787_, 0);
                                                    v_isSharedCheck_3814_ =
                                                        (!lean_is_exclusive(v___x_3787_)) as u8;
                                                    if v_isSharedCheck_3814_ == 0 {
                                                        v___x_3809_ = v___x_3787_;
                                                        v_isShared_3810_ = v_isSharedCheck_3814_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3807_);
                                                        lean_dec(v___x_3787_);
                                                        v___x_3809_ = lean_box(0);
                                                        v_isShared_3810_ = v_isSharedCheck_3814_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_3734_);
                                            lean_dec_ref(v_item_3712_);
                                            lean_dec_ref(v_config_3711_);
                                            v_a_3815_ = lean_ctor_get(v___x_3785_, 0);
                                            v_isSharedCheck_3822_ =
                                                (!lean_is_exclusive(v___x_3785_)) as u8;
                                            if v_isSharedCheck_3822_ == 0 {
                                                v___x_3817_ = v___x_3785_;
                                                v_isShared_3818_ = v_isSharedCheck_3822_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3815_);
                                                lean_dec(v___x_3785_);
                                                v___x_3817_ = lean_box(0);
                                                v_isShared_3818_ = v_isSharedCheck_3822_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_3733_);
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
                                    if lean_obj_tag(v___x_3824_) == 0 {
                                        lean_dec_ref_known(v___x_3824_, 1);
                                        v___x_3825_ = l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(
                                            v___x_3734_,
                                        );
                                        if v___x_3825_ == 0 {
                                            lean_dec_ref(v_item_3712_);
                                            lean_dec_ref(v_config_3711_);
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
                                            lean_dec_ref(v___x_3734_);
                                            v___x_3826_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                                v_item_3712_,
                                                v___y_3713_,
                                                v___y_3714_,
                                                v___y_3715_,
                                                v___y_3716_,
                                                v___y_3717_,
                                                v___y_3718_,
                                            );
                                            if lean_obj_tag(v___x_3826_) == 0 {
                                                v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
                                                v_isSharedCheck_3845_ =
                                                    (!lean_is_exclusive(v___x_3826_)) as u8;
                                                if v_isSharedCheck_3845_ == 0 {
                                                    v___x_3829_ = v___x_3826_;
                                                    v_isShared_3830_ = v_isSharedCheck_3845_;
                                                    state = 18;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3827_);
                                                    lean_dec(v___x_3826_);
                                                    v___x_3829_ = lean_box(0);
                                                    v_isShared_3830_ = v_isSharedCheck_3845_;
                                                    state = 18;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_config_3711_);
                                                v_a_3846_ = lean_ctor_get(v___x_3826_, 0);
                                                v_isSharedCheck_3853_ =
                                                    (!lean_is_exclusive(v___x_3826_)) as u8;
                                                if v_isSharedCheck_3853_ == 0 {
                                                    v___x_3848_ = v___x_3826_;
                                                    v_isShared_3849_ = v_isSharedCheck_3853_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_3846_);
                                                    lean_dec(v___x_3826_);
                                                    v___x_3848_ = lean_box(0);
                                                    v_isShared_3849_ = v_isSharedCheck_3853_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_3734_);
                                        lean_dec_ref(v_item_3712_);
                                        lean_dec_ref(v_config_3711_);
                                        v_a_3854_ = lean_ctor_get(v___x_3824_, 0);
                                        v_isSharedCheck_3861_ =
                                            (!lean_is_exclusive(v___x_3824_)) as u8;
                                        if v_isSharedCheck_3861_ == 0 {
                                            v___x_3856_ = v___x_3824_;
                                            v_isShared_3857_ = v_isSharedCheck_3861_;
                                            state = 24;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3854_);
                                            lean_dec(v___x_3824_);
                                            v___x_3856_ = lean_box(0);
                                            v_isShared_3857_ = v_isSharedCheck_3861_;
                                            state = 24;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_3733_);
                                lean_dec_ref(v_config_3711_);
                                v___x_3862_ =
                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3734_);
                                if v___x_3862_ == 0 {
                                    lean_dec_ref(v_item_3712_);
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
                                    lean_dec_ref(v___x_3734_);
                                    v_value_3863_ = lean_ctor_get(v_item_3712_, 2);
                                    lean_inc(v_value_3863_);
                                    lean_dec_ref(v_item_3712_);
                                    v___x_3864_ = l_Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0(v_value_3863_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
                                    return v___x_3864_;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3733_);
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
                            if lean_obj_tag(v___x_3866_) == 0 {
                                lean_dec_ref_known(v___x_3866_, 1);
                                v___x_3867_ =
                                    l_Lean_Elab_ConfigEval_ConfigItem_isAnonymous(v___x_3734_);
                                if v___x_3867_ == 0 {
                                    lean_dec_ref(v_item_3712_);
                                    lean_dec_ref(v_config_3711_);
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
                                    lean_dec_ref(v___x_3734_);
                                    v___x_3868_ = l_Lean_Elab_ConfigEval_evalBoolItem(
                                        v_item_3712_,
                                        v___y_3713_,
                                        v___y_3714_,
                                        v___y_3715_,
                                        v___y_3716_,
                                        v___y_3717_,
                                        v___y_3718_,
                                    );
                                    if lean_obj_tag(v___x_3868_) == 0 {
                                        v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
                                        v_isSharedCheck_3887_ =
                                            (!lean_is_exclusive(v___x_3868_)) as u8;
                                        if v_isSharedCheck_3887_ == 0 {
                                            v___x_3871_ = v___x_3868_;
                                            v_isShared_3872_ = v_isSharedCheck_3887_;
                                            state = 26;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3869_);
                                            lean_dec(v___x_3868_);
                                            v___x_3871_ = lean_box(0);
                                            v_isShared_3872_ = v_isSharedCheck_3887_;
                                            state = 26;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_config_3711_);
                                        v_a_3888_ = lean_ctor_get(v___x_3868_, 0);
                                        v_isSharedCheck_3895_ =
                                            (!lean_is_exclusive(v___x_3868_)) as u8;
                                        if v_isSharedCheck_3895_ == 0 {
                                            v___x_3890_ = v___x_3868_;
                                            v_isShared_3891_ = v_isSharedCheck_3895_;
                                            state = 30;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3888_);
                                            lean_dec(v___x_3868_);
                                            v___x_3890_ = lean_box(0);
                                            v_isShared_3891_ = v_isSharedCheck_3895_;
                                            state = 30;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_3734_);
                                lean_dec_ref(v_item_3712_);
                                lean_dec_ref(v_config_3711_);
                                v_a_3896_ = lean_ctor_get(v___x_3866_, 0);
                                v_isSharedCheck_3903_ = (!lean_is_exclusive(v___x_3866_)) as u8;
                                if v_isSharedCheck_3903_ == 0 {
                                    v___x_3898_ = v___x_3866_;
                                    v_isShared_3899_ = v_isSharedCheck_3903_;
                                    state = 32;
                                    continue;
                                } else {
                                    lean_inc(v_a_3896_);
                                    lean_dec(v___x_3866_);
                                    v___x_3898_ = lean_box(0);
                                    v_isShared_3899_ = v_isSharedCheck_3903_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_config_3711_);
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
                    lean_dec_ref(v_item_3712_);
                    lean_dec_ref(v_config_3711_);
                    v_a_3904_ = lean_ctor_get(v___x_3731_, 0);
                    v_isSharedCheck_3911_ = (!lean_is_exclusive(v___x_3731_)) as u8;
                    if v_isSharedCheck_3911_ == 0 {
                        v___x_3906_ = v___x_3731_;
                        v_isShared_3907_ = v_isSharedCheck_3911_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_a_3904_);
                        lean_dec(v___x_3731_);
                        v___x_3906_ = lean_box(0);
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
                v_grind_3753_ = lean_ctor_get_uint8(v_config_3711_, 0 as u32);
                v_star_3754_ = lean_ctor_get_uint8(v_config_3711_, 2 as u32);
                v_all_3755_ = lean_ctor_get_uint8(v_config_3711_, 3 as u32);
                v_isSharedCheck_3766_ = (!lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3766_ == 0 {
                    v___x_3757_ = v_config_3711_;
                    v_isShared_3758_ = v_isSharedCheck_3766_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v_config_3711_);
                    v___x_3757_ = lean_box(0);
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
                    v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3765_, 0 as u32, v_grind_3753_);
                    v___x_3760_ = v_reuseFailAlloc_3765_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3761_ = (lean_unbox(v_a_3749_) as u8);
                lean_dec(v_a_3749_);
                lean_ctor_set_uint8(v___x_3760_, 1 as u32, v___x_3761_);
                lean_ctor_set_uint8(v___x_3760_, 2 as u32, v_star_3754_);
                lean_ctor_set_uint8(v___x_3760_, 3 as u32, v_all_3755_);
                if v_isShared_3752_ == 0 {
                    lean_ctor_set(v___x_3751_, 0, v___x_3760_);
                    v___x_3763_ = v___x_3751_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3760_);
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
                    v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
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
                    v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
                    v___x_3781_ = v_reuseFailAlloc_3782_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3781_;
            }
            10 => {
                v_grind_3792_ = lean_ctor_get_uint8(v_config_3711_, 0 as u32);
                v_try_x3f_3793_ = lean_ctor_get_uint8(v_config_3711_, 1 as u32);
                v_all_3794_ = lean_ctor_get_uint8(v_config_3711_, 3 as u32);
                v_isSharedCheck_3805_ = (!lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3805_ == 0 {
                    v___x_3796_ = v_config_3711_;
                    v_isShared_3797_ = v_isSharedCheck_3805_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_config_3711_);
                    v___x_3796_ = lean_box(0);
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
                    v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3804_, 0 as u32, v_grind_3792_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3804_, 1 as u32, v_try_x3f_3793_);
                    v___x_3799_ = v_reuseFailAlloc_3804_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_3800_ = (lean_unbox(v_a_3788_) as u8);
                lean_dec(v_a_3788_);
                lean_ctor_set_uint8(v___x_3799_, 2 as u32, v___x_3800_);
                lean_ctor_set_uint8(v___x_3799_, 3 as u32, v_all_3794_);
                if v_isShared_3791_ == 0 {
                    lean_ctor_set(v___x_3790_, 0, v___x_3799_);
                    v___x_3802_ = v___x_3790_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3799_);
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
                    v_reuseFailAlloc_3813_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3813_, 0, v_a_3807_);
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
                    v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
                    v___x_3820_ = v_reuseFailAlloc_3821_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3820_;
            }
            18 => {
                v_try_x3f_3831_ = lean_ctor_get_uint8(v_config_3711_, 1 as u32);
                v_star_3832_ = lean_ctor_get_uint8(v_config_3711_, 2 as u32);
                v_all_3833_ = lean_ctor_get_uint8(v_config_3711_, 3 as u32);
                v_isSharedCheck_3844_ = (!lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3844_ == 0 {
                    v___x_3835_ = v_config_3711_;
                    v_isShared_3836_ = v_isSharedCheck_3844_;
                    state = 19;
                    continue;
                } else {
                    lean_dec(v_config_3711_);
                    v___x_3835_ = lean_box(0);
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
                    v_reuseFailAlloc_3843_ = lean_alloc_ctor(0, 0, (4) as u32);
                    v___x_3838_ = v_reuseFailAlloc_3843_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_3839_ = (lean_unbox(v_a_3827_) as u8);
                lean_dec(v_a_3827_);
                lean_ctor_set_uint8(v___x_3838_, 0 as u32, v___x_3839_);
                lean_ctor_set_uint8(v___x_3838_, 1 as u32, v_try_x3f_3831_);
                lean_ctor_set_uint8(v___x_3838_, 2 as u32, v_star_3832_);
                lean_ctor_set_uint8(v___x_3838_, 3 as u32, v_all_3833_);
                if v_isShared_3830_ == 0 {
                    lean_ctor_set(v___x_3829_, 0, v___x_3838_);
                    v___x_3841_ = v___x_3829_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3842_, 0, v___x_3838_);
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
                    v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
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
                    v_reuseFailAlloc_3860_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3860_, 0, v_a_3854_);
                    v___x_3859_ = v_reuseFailAlloc_3860_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3859_;
            }
            26 => {
                v_grind_3873_ = lean_ctor_get_uint8(v_config_3711_, 0 as u32);
                v_try_x3f_3874_ = lean_ctor_get_uint8(v_config_3711_, 1 as u32);
                v_star_3875_ = lean_ctor_get_uint8(v_config_3711_, 2 as u32);
                v_isSharedCheck_3886_ = (!lean_is_exclusive(v_config_3711_)) as u8;
                if v_isSharedCheck_3886_ == 0 {
                    v___x_3877_ = v_config_3711_;
                    v_isShared_3878_ = v_isSharedCheck_3886_;
                    state = 27;
                    continue;
                } else {
                    lean_dec(v_config_3711_);
                    v___x_3877_ = lean_box(0);
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
                    v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 0, (4) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3885_, 0 as u32, v_grind_3873_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3885_, 1 as u32, v_try_x3f_3874_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3885_, 2 as u32, v_star_3875_);
                    v___x_3880_ = v_reuseFailAlloc_3885_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                v___x_3881_ = (lean_unbox(v_a_3869_) as u8);
                lean_dec(v_a_3869_);
                lean_ctor_set_uint8(v___x_3880_, 3 as u32, v___x_3881_);
                if v_isShared_3872_ == 0 {
                    lean_ctor_set(v___x_3871_, 0, v___x_3880_);
                    v___x_3883_ = v___x_3871_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3884_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3884_, 0, v___x_3880_);
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
                    v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
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
                    v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
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
                    v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3910_, 0, v_a_3904_);
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
    mut v_config_3912_: *mut LeanObject,
    mut v_item_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
    mut v___y_3916_: *mut LeanObject,
    mut v___y_3917_: *mut LeanObject,
    mut v___y_3918_: *mut LeanObject,
    mut v___y_3919_: *mut LeanObject,
    mut v___y_3920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3921_: *mut LeanObject = core::ptr::null_mut();
    v_res_3921_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___lam__0(v_config_3912_, v_item_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
    lean_dec(v___y_3919_);
    lean_dec_ref(v___y_3918_);
    lean_dec(v___y_3917_);
    lean_dec_ref(v___y_3916_);
    lean_dec(v___y_3915_);
    lean_dec_ref(v___y_3914_);
    return v_res_3921_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0(
    mut v_e_3924_: *mut LeanObject,
    mut v___y_3925_: *mut LeanObject,
    mut v___y_3926_: *mut LeanObject,
    mut v___y_3927_: *mut LeanObject,
    mut v___y_3928_: *mut LeanObject,
    mut v___y_3929_: *mut LeanObject,
    mut v___y_3930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    v___x_3932_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_e_3924_, v___y_3928_);
    return v___x_3932_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___boxed(
    mut v_e_3933_: *mut LeanObject,
    mut v___y_3934_: *mut LeanObject,
    mut v___y_3935_: *mut LeanObject,
    mut v___y_3936_: *mut LeanObject,
    mut v___y_3937_: *mut LeanObject,
    mut v___y_3938_: *mut LeanObject,
    mut v___y_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3941_: *mut LeanObject = core::ptr::null_mut();
    v_res_3941_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0(v_e_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
    lean_dec(v___y_3939_);
    lean_dec_ref(v___y_3938_);
    lean_dec(v___y_3937_);
    lean_dec_ref(v___y_3936_);
    lean_dec(v___y_3935_);
    lean_dec_ref(v___y_3934_);
    return v_res_3941_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2(
    mut v_00_u03b1_3942_: *mut LeanObject,
    mut v___y_3943_: *mut LeanObject,
    mut v___y_3944_: *mut LeanObject,
    mut v___y_3945_: *mut LeanObject,
    mut v___y_3946_: *mut LeanObject,
    mut v___y_3947_: *mut LeanObject,
    mut v___y_3948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    v___x_3950_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___redArg();
    return v___x_3950_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2___boxed(
    mut v_00_u03b1_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
    mut v___y_3956_: *mut LeanObject,
    mut v___y_3957_: *mut LeanObject,
    mut v___y_3958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3959_: *mut LeanObject = core::ptr::null_mut();
    v_res_3959_ = l_Lean_Elab_throwAbortTerm___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__2(v_00_u03b1_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
    lean_dec(v___y_3957_);
    lean_dec_ref(v___y_3956_);
    lean_dec(v___y_3955_);
    lean_dec_ref(v___y_3954_);
    lean_dec(v___y_3953_);
    lean_dec_ref(v___y_3952_);
    return v_res_3959_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1(
    mut v_00_u03b1_3960_: *mut LeanObject,
    mut v_msg_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
    mut v___y_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
    mut v___y_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    v___x_3969_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___redArg(v_msg_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_);
    return v___x_3969_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1___boxed(
    mut v_00_u03b1_3970_: *mut LeanObject,
    mut v_msg_3971_: *mut LeanObject,
    mut v___y_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
    mut v___y_3974_: *mut LeanObject,
    mut v___y_3975_: *mut LeanObject,
    mut v___y_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3979_: *mut LeanObject = core::ptr::null_mut();
    v_res_3979_ = l_Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1(v_00_u03b1_3970_, v_msg_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
    lean_dec(v___y_3977_);
    lean_dec_ref(v___y_3976_);
    lean_dec(v___y_3975_);
    lean_dec_ref(v___y_3974_);
    lean_dec(v___y_3973_);
    lean_dec_ref(v___y_3972_);
    return v_res_3979_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2(
    mut v_msgData_3980_: *mut LeanObject,
    mut v_macroStack_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    v___x_3989_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___redArg(v_msgData_3980_, v_macroStack_3981_, v___y_3986_);
    return v___x_3989_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2___boxed(
    mut v_msgData_3990_: *mut LeanObject,
    mut v_macroStack_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3999_: *mut LeanObject = core::ptr::null_mut();
    v_res_3999_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__1_spec__2(v_msgData_3990_, v_macroStack_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
    lean_dec(v___y_3997_);
    lean_dec_ref(v___y_3996_);
    lean_dec(v___y_3995_);
    lean_dec_ref(v___y_3994_);
    lean_dec(v___y_3993_);
    lean_dec_ref(v___y_3992_);
    return v_res_3999_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0()
-> *mut LeanObject {
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    v___x_4000_ = lean_box(0);
    v___x_4001_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__5;
    v___x_4002_ = l_Lean_mkConst(v___x_4001_, v___x_4000_);
    return v___x_4002_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    v___x_4003_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0_once
        ),
        _init_l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0___closed__0,
    );
    v___x_4004_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4004_, 0, v___x_4003_);
    return v___x_4004_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___lam__0(
    mut v_cfg_4005_: *mut LeanObject,
    mut v_cfgItem_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
    mut v___y_4009_: *mut LeanObject,
    mut v___y_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    v___x_4014_ = lean_obj_once(
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
    mut v_cfg_4016_: *mut LeanObject,
    mut v_cfgItem_4017_: *mut LeanObject,
    mut v___y_4018_: *mut LeanObject,
    mut v___y_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
    mut v___y_4021_: *mut LeanObject,
    mut v___y_4022_: *mut LeanObject,
    mut v___y_4023_: *mut LeanObject,
    mut v___y_4024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4025_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4023_);
    lean_dec_ref(v___y_4022_);
    lean_dec(v___y_4021_);
    lean_dec_ref(v___y_4020_);
    lean_dec(v___y_4019_);
    lean_dec_ref(v___y_4018_);
    lean_dec(v_cfgItem_4017_);
    return v_res_4025_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
    mut v_cfg_4027_: *mut LeanObject,
    mut v_init_4028_: *mut LeanObject,
    mut v_logExceptions_4029_: u8,
    mut v_a_4030_: *mut LeanObject,
    mut v_a_4031_: *mut LeanObject,
    mut v_a_4032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_onErr_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eval_4035_: *mut LeanObject = core::ptr::null_mut();
    v_onErr_4034_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg___closed__0;
    v_eval_4035_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem___closed__0;
    if v_logExceptions_4029_ == 0 {
        let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
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
        let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
        v_recover_4037_ = lean_ctor_get_uint8(
            v_a_4030_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_cfg_4039_: *mut LeanObject,
    mut v_init_4040_: *mut LeanObject,
    mut v_logExceptions_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
    mut v_a_4043_: *mut LeanObject,
    mut v_a_4044_: *mut LeanObject,
    mut v_a_4045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_4046_: u8 = 0;
    let mut v_res_4047_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_4046_ = (lean_unbox(v_logExceptions_4041_) as u8);
    v_res_4047_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
        v_cfg_4039_,
        v_init_4040_,
        v_logExceptions_boxed_4046_,
        v_a_4042_,
        v_a_4043_,
        v_a_4044_,
    );
    lean_dec(v_a_4044_);
    lean_dec_ref(v_a_4043_);
    lean_dec_ref(v_a_4042_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig(
    mut v_cfg_4048_: *mut LeanObject,
    mut v_init_4049_: *mut LeanObject,
    mut v_logExceptions_4050_: u8,
    mut v_a_4051_: *mut LeanObject,
    mut v_a_4052_: *mut LeanObject,
    mut v_a_4053_: *mut LeanObject,
    mut v_a_4054_: *mut LeanObject,
    mut v_a_4055_: *mut LeanObject,
    mut v_a_4056_: *mut LeanObject,
    mut v_a_4057_: *mut LeanObject,
    mut v_a_4058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_cfg_4061_: *mut LeanObject,
    mut v_init_4062_: *mut LeanObject,
    mut v_logExceptions_4063_: *mut LeanObject,
    mut v_a_4064_: *mut LeanObject,
    mut v_a_4065_: *mut LeanObject,
    mut v_a_4066_: *mut LeanObject,
    mut v_a_4067_: *mut LeanObject,
    mut v_a_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
    mut v_a_4071_: *mut LeanObject,
    mut v_a_4072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_logExceptions_boxed_4073_: u8 = 0;
    let mut v_res_4074_: *mut LeanObject = core::ptr::null_mut();
    v_logExceptions_boxed_4073_ = (lean_unbox(v_logExceptions_4063_) as u8);
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
    lean_dec(v_a_4071_);
    lean_dec_ref(v_a_4070_);
    lean_dec(v_a_4069_);
    lean_dec_ref(v_a_4068_);
    lean_dec(v_a_4067_);
    lean_dec_ref(v_a_4066_);
    lean_dec(v_a_4065_);
    lean_dec_ref(v_a_4064_);
    return v_res_4074_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(
    mut v_e_4075_: *mut LeanObject,
    mut v___y_4076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4098_: u8 = 0;
    let mut v_unused_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4078_ = l_Lean_Expr_hasMVar(v_e_4075_);
                if v___x_4078_ == 0 {
                    v___x_4079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4079_, 0, v_e_4075_);
                    return v___x_4079_;
                } else {
                    v___x_4080_ = lean_st_ref_get(v___y_4076_);
                    v_mctx_4081_ = lean_ctor_get(v___x_4080_, 0);
                    lean_inc_ref(v_mctx_4081_);
                    lean_dec(v___x_4080_);
                    v___x_4082_ = l_Lean_instantiateMVarsCore(v_mctx_4081_, v_e_4075_);
                    v_fst_4083_ = lean_ctor_get(v___x_4082_, 0);
                    lean_inc(v_fst_4083_);
                    v_snd_4084_ = lean_ctor_get(v___x_4082_, 1);
                    lean_inc(v_snd_4084_);
                    lean_dec_ref(v___x_4082_);
                    v___x_4085_ = lean_st_ref_take(v___y_4076_);
                    v_cache_4086_ = lean_ctor_get(v___x_4085_, 1);
                    v_zetaDeltaFVarIds_4087_ = lean_ctor_get(v___x_4085_, 2);
                    v_postponed_4088_ = lean_ctor_get(v___x_4085_, 3);
                    v_diag_4089_ = lean_ctor_get(v___x_4085_, 4);
                    v_isSharedCheck_4098_ = (!lean_is_exclusive(v___x_4085_)) as u8;
                    if v_isSharedCheck_4098_ == 0 {
                        v_unused_4099_ = lean_ctor_get(v___x_4085_, 0);
                        lean_dec(v_unused_4099_);
                        v___x_4091_ = v___x_4085_;
                        v_isShared_4092_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4089_);
                        lean_inc(v_postponed_4088_);
                        lean_inc(v_zetaDeltaFVarIds_4087_);
                        lean_inc(v_cache_4086_);
                        lean_dec(v___x_4085_);
                        v___x_4091_ = lean_box(0);
                        v_isShared_4092_ = v_isSharedCheck_4098_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4092_ == 0 {
                    lean_ctor_set(v___x_4091_, 0, v_snd_4084_);
                    v___x_4094_ = v___x_4091_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4097_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_snd_4084_);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 1, v_cache_4086_);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 2, v_zetaDeltaFVarIds_4087_);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 3, v_postponed_4088_);
                    lean_ctor_set(v_reuseFailAlloc_4097_, 4, v_diag_4089_);
                    v___x_4094_ = v_reuseFailAlloc_4097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4095_ = lean_st_ref_set(v___y_4076_, v___x_4094_);
                v___x_4096_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4096_, 0, v_fst_4083_);
                return v___x_4096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg___boxed(
    mut v_e_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4103_: *mut LeanObject = core::ptr::null_mut();
    v_res_4103_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(
            v_e_4100_,
            v___y_4101_,
        );
    lean_dec(v___y_4101_);
    return v_res_4103_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0(
    mut v_e_4104_: *mut LeanObject,
    mut v___y_4105_: *mut LeanObject,
    mut v___y_4106_: *mut LeanObject,
    mut v___y_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    v___x_4114_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(
            v_e_4104_,
            v___y_4110_,
        );
    return v___x_4114_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___boxed(
    mut v_e_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
    mut v___y_4123_: *mut LeanObject,
    mut v___y_4124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4125_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4123_);
    lean_dec_ref(v___y_4122_);
    lean_dec(v___y_4121_);
    lean_dec_ref(v___y_4120_);
    lean_dec(v___y_4119_);
    lean_dec_ref(v___y_4118_);
    lean_dec(v___y_4117_);
    lean_dec_ref(v___y_4116_);
    return v_res_4125_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0(
    mut v_x_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
    mut v___y_4133_: *mut LeanObject,
    mut v___y_4134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_4130_);
    lean_inc_ref(v___y_4129_);
    lean_inc(v___y_4128_);
    lean_inc_ref(v___y_4127_);
    v___x_4136_ = lean_apply_9(
        v_x_4126_,
        v___y_4127_,
        v___y_4128_,
        v___y_4129_,
        v___y_4130_,
        v___y_4131_,
        v___y_4132_,
        v___y_4133_,
        v___y_4134_,
        lean_box(0),
    );
    return v___x_4136_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0___boxed(
    mut v_x_4137_: *mut LeanObject,
    mut v___y_4138_: *mut LeanObject,
    mut v___y_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4147_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4141_);
    lean_dec_ref(v___y_4140_);
    lean_dec(v___y_4139_);
    lean_dec_ref(v___y_4138_);
    return v_res_4147_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(
    mut v_mctx_4148_: *mut LeanObject,
    mut v_x_4149_: *mut LeanObject,
    mut v___y_4150_: *mut LeanObject,
    mut v___y_4151_: *mut LeanObject,
    mut v___y_4152_: *mut LeanObject,
    mut v___y_4153_: *mut LeanObject,
    mut v___y_4154_: *mut LeanObject,
    mut v___y_4155_: *mut LeanObject,
    mut v___y_4156_: *mut LeanObject,
    mut v___y_4157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4153_);
                lean_inc_ref(v___y_4152_);
                lean_inc(v___y_4151_);
                lean_inc_ref(v___y_4150_);
                v___f_4159_ = lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_4159_, 0, v_x_4149_);
                lean_closure_set(v___f_4159_, 1, v___y_4150_);
                lean_closure_set(v___f_4159_, 2, v___y_4151_);
                lean_closure_set(v___f_4159_, 3, v___y_4152_);
                lean_closure_set(v___f_4159_, 4, v___y_4153_);
                v___x_4160_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMCtxImp(
                    lean_box(0),
                    v_mctx_4148_,
                    v___f_4159_,
                    v___y_4154_,
                    v___y_4155_,
                    v___y_4156_,
                    v___y_4157_,
                );
                if lean_obj_tag(v___x_4160_) == 0 {
                    return v___x_4160_;
                } else {
                    v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
                    v_isSharedCheck_4168_ = (!lean_is_exclusive(v___x_4160_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4163_ = v___x_4160_;
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4161_);
                        lean_dec(v___x_4160_);
                        v___x_4163_ = lean_box(0);
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
                    v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
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
    mut v_mctx_4169_: *mut LeanObject,
    mut v_x_4170_: *mut LeanObject,
    mut v___y_4171_: *mut LeanObject,
    mut v___y_4172_: *mut LeanObject,
    mut v___y_4173_: *mut LeanObject,
    mut v___y_4174_: *mut LeanObject,
    mut v___y_4175_: *mut LeanObject,
    mut v___y_4176_: *mut LeanObject,
    mut v___y_4177_: *mut LeanObject,
    mut v___y_4178_: *mut LeanObject,
    mut v___y_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4180_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4178_);
    lean_dec_ref(v___y_4177_);
    lean_dec(v___y_4176_);
    lean_dec_ref(v___y_4175_);
    lean_dec(v___y_4174_);
    lean_dec_ref(v___y_4173_);
    lean_dec(v___y_4172_);
    lean_dec_ref(v___y_4171_);
    return v_res_4180_;
}
pub unsafe fn l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1(
    mut v_00_u03b1_4181_: *mut LeanObject,
    mut v_mctx_4182_: *mut LeanObject,
    mut v_x_4183_: *mut LeanObject,
    mut v___y_4184_: *mut LeanObject,
    mut v___y_4185_: *mut LeanObject,
    mut v___y_4186_: *mut LeanObject,
    mut v___y_4187_: *mut LeanObject,
    mut v___y_4188_: *mut LeanObject,
    mut v___y_4189_: *mut LeanObject,
    mut v___y_4190_: *mut LeanObject,
    mut v___y_4191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4194_: *mut LeanObject,
    mut v_mctx_4195_: *mut LeanObject,
    mut v_x_4196_: *mut LeanObject,
    mut v___y_4197_: *mut LeanObject,
    mut v___y_4198_: *mut LeanObject,
    mut v___y_4199_: *mut LeanObject,
    mut v___y_4200_: *mut LeanObject,
    mut v___y_4201_: *mut LeanObject,
    mut v___y_4202_: *mut LeanObject,
    mut v___y_4203_: *mut LeanObject,
    mut v___y_4204_: *mut LeanObject,
    mut v___y_4205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4206_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4204_);
    lean_dec_ref(v___y_4203_);
    lean_dec(v___y_4202_);
    lean_dec_ref(v___y_4201_);
    lean_dec(v___y_4200_);
    lean_dec_ref(v___y_4199_);
    lean_dec(v___y_4198_);
    lean_dec_ref(v___y_4197_);
    return v_res_4206_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg(
    mut v_e_4207_: *mut LeanObject,
    mut v___y_4208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4210_: u8 = 0;
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v_unused_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4210_ = l_Lean_Expr_hasMVar(v_e_4207_);
                if v___x_4210_ == 0 {
                    v___x_4211_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4211_, 0, v_e_4207_);
                    return v___x_4211_;
                } else {
                    v___x_4212_ = lean_st_ref_get(v___y_4208_);
                    v_mctx_4213_ = lean_ctor_get(v___x_4212_, 0);
                    lean_inc_ref(v_mctx_4213_);
                    lean_dec(v___x_4212_);
                    v___x_4214_ = l_Lean_instantiateMVarsCore(v_mctx_4213_, v_e_4207_);
                    v_fst_4215_ = lean_ctor_get(v___x_4214_, 0);
                    lean_inc(v_fst_4215_);
                    v_snd_4216_ = lean_ctor_get(v___x_4214_, 1);
                    lean_inc(v_snd_4216_);
                    lean_dec_ref(v___x_4214_);
                    v___x_4217_ = lean_st_ref_take(v___y_4208_);
                    v_cache_4218_ = lean_ctor_get(v___x_4217_, 1);
                    v_zetaDeltaFVarIds_4219_ = lean_ctor_get(v___x_4217_, 2);
                    v_postponed_4220_ = lean_ctor_get(v___x_4217_, 3);
                    v_diag_4221_ = lean_ctor_get(v___x_4217_, 4);
                    v_isSharedCheck_4230_ = (!lean_is_exclusive(v___x_4217_)) as u8;
                    if v_isSharedCheck_4230_ == 0 {
                        v_unused_4231_ = lean_ctor_get(v___x_4217_, 0);
                        lean_dec(v_unused_4231_);
                        v___x_4223_ = v___x_4217_;
                        v_isShared_4224_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4221_);
                        lean_inc(v_postponed_4220_);
                        lean_inc(v_zetaDeltaFVarIds_4219_);
                        lean_inc(v_cache_4218_);
                        lean_dec(v___x_4217_);
                        v___x_4223_ = lean_box(0);
                        v_isShared_4224_ = v_isSharedCheck_4230_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4224_ == 0 {
                    lean_ctor_set(v___x_4223_, 0, v_snd_4216_);
                    v___x_4226_ = v___x_4223_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_snd_4216_);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 1, v_cache_4218_);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 2, v_zetaDeltaFVarIds_4219_);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 3, v_postponed_4220_);
                    lean_ctor_set(v_reuseFailAlloc_4229_, 4, v_diag_4221_);
                    v___x_4226_ = v_reuseFailAlloc_4229_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4227_ = lean_st_ref_set(v___y_4208_, v___x_4226_);
                v___x_4228_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4228_, 0, v_fst_4215_);
                return v___x_4228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg___boxed(
    mut v_e_4232_: *mut LeanObject,
    mut v___y_4233_: *mut LeanObject,
    mut v___y_4234_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4235_: *mut LeanObject = core::ptr::null_mut();
    v_res_4235_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg(
            v_e_4232_,
            v___y_4233_,
        );
    lean_dec(v___y_4233_);
    return v_res_4235_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4(
    mut v_e_4236_: *mut LeanObject,
    mut v___y_4237_: *mut LeanObject,
    mut v___y_4238_: *mut LeanObject,
    mut v___y_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    v___x_4242_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___redArg(
            v_e_4236_,
            v___y_4238_,
        );
    return v___x_4242_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___boxed(
    mut v_e_4243_: *mut LeanObject,
    mut v___y_4244_: *mut LeanObject,
    mut v___y_4245_: *mut LeanObject,
    mut v___y_4246_: *mut LeanObject,
    mut v___y_4247_: *mut LeanObject,
    mut v___y_4248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4249_: *mut LeanObject = core::ptr::null_mut();
    v_res_4249_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4(
        v_e_4243_,
        v___y_4244_,
        v___y_4245_,
        v___y_4246_,
        v___y_4247_,
    );
    lean_dec(v___y_4247_);
    lean_dec_ref(v___y_4246_);
    lean_dec(v___y_4245_);
    lean_dec_ref(v___y_4244_);
    return v_res_4249_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg(
    mut v_mvarId_4250_: *mut LeanObject,
    mut v_x_4251_: *mut LeanObject,
    mut v___y_4252_: *mut LeanObject,
    mut v___y_4253_: *mut LeanObject,
    mut v___y_4254_: *mut LeanObject,
    mut v___y_4255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4261_: u8 = 0;
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4265_: u8 = 0;
    let mut v_a_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4269_: u8 = 0;
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4257_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4250_,
                    v_x_4251_,
                    v___y_4252_,
                    v___y_4253_,
                    v___y_4254_,
                    v___y_4255_,
                );
                if lean_obj_tag(v___x_4257_) == 0 {
                    v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
                    v_isSharedCheck_4265_ = (!lean_is_exclusive(v___x_4257_)) as u8;
                    if v_isSharedCheck_4265_ == 0 {
                        v___x_4260_ = v___x_4257_;
                        v_isShared_4261_ = v_isSharedCheck_4265_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4258_);
                        lean_dec(v___x_4257_);
                        v___x_4260_ = lean_box(0);
                        v_isShared_4261_ = v_isSharedCheck_4265_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4266_ = lean_ctor_get(v___x_4257_, 0);
                    v_isSharedCheck_4273_ = (!lean_is_exclusive(v___x_4257_)) as u8;
                    if v_isSharedCheck_4273_ == 0 {
                        v___x_4268_ = v___x_4257_;
                        v_isShared_4269_ = v_isSharedCheck_4273_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4266_);
                        lean_dec(v___x_4257_);
                        v___x_4268_ = lean_box(0);
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
                    v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4258_);
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
                    v_reuseFailAlloc_4272_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4272_, 0, v_a_4266_);
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
    mut v_mvarId_4274_: *mut LeanObject,
    mut v_x_4275_: *mut LeanObject,
    mut v___y_4276_: *mut LeanObject,
    mut v___y_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
    mut v___y_4279_: *mut LeanObject,
    mut v___y_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4281_: *mut LeanObject = core::ptr::null_mut();
    v_res_4281_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg(
            v_mvarId_4274_,
            v_x_4275_,
            v___y_4276_,
            v___y_4277_,
            v___y_4278_,
            v___y_4279_,
        );
    lean_dec(v___y_4279_);
    lean_dec_ref(v___y_4278_);
    lean_dec(v___y_4277_);
    lean_dec_ref(v___y_4276_);
    return v_res_4281_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5(
    mut v_00_u03b1_4282_: *mut LeanObject,
    mut v_mvarId_4283_: *mut LeanObject,
    mut v_x_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4290_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4291_: *mut LeanObject,
    mut v_mvarId_4292_: *mut LeanObject,
    mut v_x_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4299_: *mut LeanObject = core::ptr::null_mut();
    v_res_4299_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5(
        v_00_u03b1_4291_,
        v_mvarId_4292_,
        v_x_4293_,
        v___y_4294_,
        v___y_4295_,
        v___y_4296_,
        v___y_4297_,
    );
    lean_dec(v___y_4297_);
    lean_dec_ref(v___y_4296_);
    lean_dec(v___y_4295_);
    lean_dec_ref(v___y_4294_);
    return v_res_4299_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___redArg(
    mut v_mvarId_4300_: *mut LeanObject,
    mut v_x_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
    mut v___y_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4316_: u8 = 0;
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_4305_);
                lean_inc_ref(v___y_4304_);
                lean_inc(v___y_4303_);
                lean_inc_ref(v___y_4302_);
                v___f_4311_ = lean_alloc_closure(l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_4311_, 0, v_x_4301_);
                lean_closure_set(v___f_4311_, 1, v___y_4302_);
                lean_closure_set(v___f_4311_, 2, v___y_4303_);
                lean_closure_set(v___f_4311_, 3, v___y_4304_);
                lean_closure_set(v___f_4311_, 4, v___y_4305_);
                v___x_4312_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4300_,
                    v___f_4311_,
                    v___y_4306_,
                    v___y_4307_,
                    v___y_4308_,
                    v___y_4309_,
                );
                if lean_obj_tag(v___x_4312_) == 0 {
                    return v___x_4312_;
                } else {
                    v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4320_ = (!lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4320_ == 0 {
                        v___x_4315_ = v___x_4312_;
                        v_isShared_4316_ = v_isSharedCheck_4320_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4313_);
                        lean_dec(v___x_4312_);
                        v___x_4315_ = lean_box(0);
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
                    v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
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
    mut v_mvarId_4321_: *mut LeanObject,
    mut v_x_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
    mut v___y_4329_: *mut LeanObject,
    mut v___y_4330_: *mut LeanObject,
    mut v___y_4331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4332_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4330_);
    lean_dec_ref(v___y_4329_);
    lean_dec(v___y_4328_);
    lean_dec_ref(v___y_4327_);
    lean_dec(v___y_4326_);
    lean_dec_ref(v___y_4325_);
    lean_dec(v___y_4324_);
    lean_dec_ref(v___y_4323_);
    return v_res_4332_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12(
    mut v_00_u03b1_4333_: *mut LeanObject,
    mut v_mvarId_4334_: *mut LeanObject,
    mut v_x_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
    mut v___y_4339_: *mut LeanObject,
    mut v___y_4340_: *mut LeanObject,
    mut v___y_4341_: *mut LeanObject,
    mut v___y_4342_: *mut LeanObject,
    mut v___y_4343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_4346_: *mut LeanObject,
    mut v_mvarId_4347_: *mut LeanObject,
    mut v_x_4348_: *mut LeanObject,
    mut v___y_4349_: *mut LeanObject,
    mut v___y_4350_: *mut LeanObject,
    mut v___y_4351_: *mut LeanObject,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
    mut v___y_4354_: *mut LeanObject,
    mut v___y_4355_: *mut LeanObject,
    mut v___y_4356_: *mut LeanObject,
    mut v___y_4357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4358_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4356_);
    lean_dec_ref(v___y_4355_);
    lean_dec(v___y_4354_);
    lean_dec_ref(v___y_4353_);
    lean_dec(v___y_4352_);
    lean_dec_ref(v___y_4351_);
    lean_dec(v___y_4350_);
    lean_dec_ref(v___y_4349_);
    return v_res_4358_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__0(
    mut v___x_4359_: *mut LeanObject,
    mut v_grind_4360_: u8,
    mut v_try_x3f_4361_: u8,
    mut v_goals_4362_: *mut LeanObject,
    mut v___y_4363_: *mut LeanObject,
    mut v___y_4364_: *mut LeanObject,
    mut v___y_4365_: *mut LeanObject,
    mut v___y_4366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    v___x_4368_ = 0;
    v___x_4369_ = lean_unsigned_to_nat(6);
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
    mut v___x_4371_: *mut LeanObject,
    mut v_grind_4372_: *mut LeanObject,
    mut v_try_x3f_4373_: *mut LeanObject,
    mut v_goals_4374_: *mut LeanObject,
    mut v___y_4375_: *mut LeanObject,
    mut v___y_4376_: *mut LeanObject,
    mut v___y_4377_: *mut LeanObject,
    mut v___y_4378_: *mut LeanObject,
    mut v___y_4379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_grind_boxed_4380_: u8 = 0;
    let mut v_try_x3f_boxed_4381_: u8 = 0;
    let mut v_res_4382_: *mut LeanObject = core::ptr::null_mut();
    v_grind_boxed_4380_ = (lean_unbox(v_grind_4372_) as u8);
    v_try_x3f_boxed_4381_ = (lean_unbox(v_try_x3f_4373_) as u8);
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
    lean_dec(v___y_4378_);
    lean_dec_ref(v___y_4377_);
    lean_dec(v___y_4376_);
    lean_dec_ref(v___y_4375_);
    return v_res_4382_;
}
pub unsafe fn l_List_all___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__6(
    mut v_a_4383_: *mut LeanObject,
    mut v_x_4384_: *mut LeanObject,
) -> u8 {
    let mut v___x_4385_: u8 = 0;
    let mut v_head_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4384_) == 0 {
                    v___x_4385_ = 1;
                    return v___x_4385_;
                } else {
                    v_head_4386_ = lean_ctor_get(v_x_4384_, 0);
                    lean_inc(v_head_4386_);
                    v_tail_4387_ = lean_ctor_get(v_x_4384_, 1);
                    lean_inc(v_tail_4387_);
                    lean_dec_ref_known(v_x_4384_, 2);
                    v___x_4388_ = l_Lean_Expr_occurs(v_head_4386_, v_a_4383_);
                    if v___x_4388_ == 0 {
                        lean_dec(v_tail_4387_);
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
    mut v_a_4390_: *mut LeanObject,
    mut v_x_4391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4392_: u8 = 0;
    let mut v_r_4393_: *mut LeanObject = core::ptr::null_mut();
    v_res_4392_ =
        l_List_all___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__6(v_a_4390_, v_x_4391_);
    lean_dec_ref(v_a_4390_);
    v_r_4393_ = lean_box((v_res_4392_) as usize);
    return v_r_4393_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__1(
    mut v___x_4394_: *mut LeanObject,
    mut v_g_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4407_: u8 = 0;
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4413_: u8 = 0;
    let mut v_a_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4417_: u8 = 0;
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4421_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_g_4395_);
                v___x_4401_ = l_Lean_Expr_mvar___override(v_g_4395_);
                v___x_4402_ = lean_alloc_closure(l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__4___boxed as *mut core::ffi::c_void, 6, 1);
                lean_closure_set(v___x_4402_, 0, v___x_4401_);
                v___x_4403_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__5___redArg(v_g_4395_, v___x_4402_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_);
                if lean_obj_tag(v___x_4403_) == 0 {
                    v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
                    v_isSharedCheck_4413_ = (!lean_is_exclusive(v___x_4403_)) as u8;
                    if v_isSharedCheck_4413_ == 0 {
                        v___x_4406_ = v___x_4403_;
                        v_isShared_4407_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4404_);
                        lean_dec(v___x_4403_);
                        v___x_4406_ = lean_box(0);
                        v_isShared_4407_ = v_isSharedCheck_4413_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4394_);
                    v_a_4414_ = lean_ctor_get(v___x_4403_, 0);
                    v_isSharedCheck_4421_ = (!lean_is_exclusive(v___x_4403_)) as u8;
                    if v_isSharedCheck_4421_ == 0 {
                        v___x_4416_ = v___x_4403_;
                        v_isShared_4417_ = v_isSharedCheck_4421_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4414_);
                        lean_dec(v___x_4403_);
                        v___x_4416_ = lean_box(0);
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
                lean_dec(v_a_4404_);
                v___x_4409_ = lean_box((v___x_4408_) as usize);
                if v_isShared_4407_ == 0 {
                    lean_ctor_set(v___x_4406_, 0, v___x_4409_);
                    v___x_4411_ = v___x_4406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4412_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4412_, 0, v___x_4409_);
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
                    v_reuseFailAlloc_4420_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
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
    mut v___x_4422_: *mut LeanObject,
    mut v_g_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
    mut v___y_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4429_: *mut LeanObject = core::ptr::null_mut();
    v_res_4429_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__1(
        v___x_4422_,
        v_g_4423_,
        v___y_4424_,
        v___y_4425_,
        v___y_4426_,
        v___y_4427_,
    );
    lean_dec(v___y_4427_);
    lean_dec_ref(v___y_4426_);
    lean_dec(v___y_4425_);
    lean_dec_ref(v___y_4424_);
    return v_res_4429_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg(
    mut v_msg_4430_: *mut LeanObject,
    mut v___y_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
    mut v___y_4433_: *mut LeanObject,
    mut v___y_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4441_: u8 = 0;
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4436_ = lean_ctor_get(v___y_4433_, 5);
                v___x_4437_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v_msg_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
                v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
                v_isSharedCheck_4446_ = (!lean_is_exclusive(v___x_4437_)) as u8;
                if v_isSharedCheck_4446_ == 0 {
                    v___x_4440_ = v___x_4437_;
                    v_isShared_4441_ = v_isSharedCheck_4446_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4438_);
                    lean_dec(v___x_4437_);
                    v___x_4440_ = lean_box(0);
                    v_isShared_4441_ = v_isSharedCheck_4446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4436_);
                v___x_4442_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4442_, 0, v_ref_4436_);
                lean_ctor_set(v___x_4442_, 1, v_a_4438_);
                if v_isShared_4441_ == 0 {
                    lean_ctor_set_tag(v___x_4440_, 1);
                    lean_ctor_set(v___x_4440_, 0, v___x_4442_);
                    v___x_4444_ = v___x_4440_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4445_, 0, v___x_4442_);
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
    mut v_msg_4447_: *mut LeanObject,
    mut v___y_4448_: *mut LeanObject,
    mut v___y_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
    mut v___y_4452_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4453_: *mut LeanObject = core::ptr::null_mut();
    v_res_4453_ = l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11___redArg(
        v_msg_4447_,
        v___y_4448_,
        v___y_4449_,
        v___y_4450_,
        v___y_4451_,
    );
    lean_dec(v___y_4451_);
    lean_dec_ref(v___y_4450_);
    lean_dec(v___y_4449_);
    lean_dec_ref(v___y_4448_);
    return v_res_4453_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__7(
    mut v_as_4454_: *mut LeanObject,
    mut v_sz_4455_: usize,
    mut v_i_4456_: usize,
    mut v_b_4457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: usize = 0;
    let mut v___x_4461_: usize = 0;
    let mut v___x_4463_: u8 = 0;
    let mut v_fst_4464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4468_: u8 = 0;
    let mut v_a_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: u8 = 0;
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4463_ = lean_usize_dec_lt(v_i_4456_, v_sz_4455_);
                if v___x_4463_ == 0 {
                    return v_b_4457_;
                } else {
                    v_fst_4464_ = lean_ctor_get(v_b_4457_, 0);
                    v_snd_4465_ = lean_ctor_get(v_b_4457_, 1);
                    v_isSharedCheck_4480_ = (!lean_is_exclusive(v_b_4457_)) as u8;
                    if v_isSharedCheck_4480_ == 0 {
                        v___x_4467_ = v_b_4457_;
                        v_isShared_4468_ = v_isSharedCheck_4480_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_4465_);
                        lean_inc(v_fst_4464_);
                        lean_dec(v_b_4457_);
                        v___x_4467_ = lean_box(0);
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
                v_fst_4470_ = lean_ctor_get(v_a_4469_, 0);
                v___x_4471_ = l_List_isEmpty___redArg(v_fst_4470_);
                if v___x_4471_ == 0 {
                    lean_inc(v_a_4469_);
                    v___x_4472_ = lean_array_push(v_snd_4465_, v_a_4469_);
                    if v_isShared_4468_ == 0 {
                        lean_ctor_set(v___x_4467_, 1, v___x_4472_);
                        v___x_4474_ = v___x_4467_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_fst_4464_);
                        lean_ctor_set(v_reuseFailAlloc_4475_, 1, v___x_4472_);
                        v___x_4474_ = v_reuseFailAlloc_4475_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_inc(v_a_4469_);
                    v___x_4476_ = lean_array_push(v_fst_4464_, v_a_4469_);
                    if v_isShared_4468_ == 0 {
                        lean_ctor_set(v___x_4467_, 0, v___x_4476_);
                        v___x_4478_ = v___x_4467_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4479_, 0, v___x_4476_);
                        lean_ctor_set(v_reuseFailAlloc_4479_, 1, v_snd_4465_);
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
    mut v_as_4481_: *mut LeanObject,
    mut v_sz_4482_: *mut LeanObject,
    mut v_i_4483_: *mut LeanObject,
    mut v_b_4484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4485_: usize = 0;
    let mut v_i_boxed_4486_: usize = 0;
    let mut v_res_4487_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4485_ = lean_unbox_usize(v_sz_4482_);
    lean_dec(v_sz_4482_);
    v_i_boxed_4486_ = lean_unbox_usize(v_i_4483_);
    lean_dec(v_i_4483_);
    v_res_4487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__7(v_as_4481_, v_sz_boxed_4485_, v_i_boxed_4486_, v_b_4484_);
    lean_dec_ref(v_as_4481_);
    return v_res_4487_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___lam__0(
    mut v___x_4488_: *mut LeanObject,
    mut v_a_4489_: *mut LeanObject,
    mut v_ref_4490_: *mut LeanObject,
    mut v___x_4491_: u8,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
    mut v___y_4494_: *mut LeanObject,
    mut v___y_4495_: *mut LeanObject,
    mut v___y_4496_: *mut LeanObject,
    mut v___y_4497_: *mut LeanObject,
    mut v___y_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4501_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(v___x_4488_, v___y_4497_);
                if lean_obj_tag(v___x_4501_) == 0 {
                    v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
                    lean_inc(v_a_4502_);
                    lean_dec_ref_known(v___x_4501_, 1);
                    v___x_4503_ = l_Lean_Expr_headBeta(v_a_4502_);
                    v___x_4504_ = lean_box(0);
                    v___x_4505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4505_, 0, v_a_4489_);
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
                    lean_dec(v_ref_4490_);
                    lean_dec_ref(v_a_4489_);
                    v_a_4507_ = lean_ctor_get(v___x_4501_, 0);
                    v_isSharedCheck_4514_ = (!lean_is_exclusive(v___x_4501_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4509_ = v___x_4501_;
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4507_);
                        lean_dec(v___x_4501_);
                        v___x_4509_ = lean_box(0);
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
                    v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
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
    mut v___x_4515_: *mut LeanObject,
    mut v_a_4516_: *mut LeanObject,
    mut v_ref_4517_: *mut LeanObject,
    mut v___x_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
    mut v___y_4520_: *mut LeanObject,
    mut v___y_4521_: *mut LeanObject,
    mut v___y_4522_: *mut LeanObject,
    mut v___y_4523_: *mut LeanObject,
    mut v___y_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_20785__boxed_4528_: u8 = 0;
    let mut v_res_4529_: *mut LeanObject = core::ptr::null_mut();
    v___x_20785__boxed_4528_ = (lean_unbox(v___x_4518_) as u8);
    v_res_4529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___lam__0(v___x_4515_, v_a_4516_, v_ref_4517_, v___x_20785__boxed_4528_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
    lean_dec(v___y_4526_);
    lean_dec_ref(v___y_4525_);
    lean_dec(v___y_4524_);
    lean_dec_ref(v___y_4523_);
    lean_dec(v___y_4522_);
    lean_dec_ref(v___y_4521_);
    lean_dec(v___y_4520_);
    lean_dec_ref(v___y_4519_);
    return v_res_4529_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8(
    mut v_a_4530_: *mut LeanObject,
    mut v_a_4531_: *mut LeanObject,
    mut v_ref_4532_: *mut LeanObject,
    mut v_as_4533_: *mut LeanObject,
    mut v_sz_4534_: usize,
    mut v_i_4535_: usize,
    mut v_b_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
    mut v___y_4538_: *mut LeanObject,
    mut v___y_4539_: *mut LeanObject,
    mut v___y_4540_: *mut LeanObject,
    mut v___y_4541_: *mut LeanObject,
    mut v___y_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4546_: u8 = 0;
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: usize = 0;
    let mut v___x_4556_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4546_ = lean_usize_dec_lt(v_i_4535_, v_sz_4534_);
                if v___x_4546_ == 0 {
                    lean_dec(v_ref_4532_);
                    lean_dec_ref(v_a_4531_);
                    lean_dec(v_a_4530_);
                    v___x_4547_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4547_, 0, v_b_4536_);
                    return v___x_4547_;
                } else {
                    v_a_4548_ = lean_array_uget_borrowed(v_as_4533_, v_i_4535_);
                    v_snd_4549_ = lean_ctor_get(v_a_4548_, 1);
                    lean_inc(v_a_4530_);
                    v___x_4550_ = l_Lean_mkMVar(v_a_4530_);
                    v___x_4551_ = lean_box((v___x_4546_) as usize);
                    lean_inc(v_ref_4532_);
                    lean_inc_ref(v_a_4531_);
                    v___f_4552_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___lam__0___boxed as *mut core::ffi::c_void, 13, 4);
                    lean_closure_set(v___f_4552_, 0, v___x_4550_);
                    lean_closure_set(v___f_4552_, 1, v_a_4531_);
                    lean_closure_set(v___f_4552_, 2, v_ref_4532_);
                    lean_closure_set(v___f_4552_, 3, v___x_4551_);
                    lean_inc(v_snd_4549_);
                    v___x_4553_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(v_snd_4549_, v___f_4552_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
                    if lean_obj_tag(v___x_4553_) == 0 {
                        lean_dec_ref_known(v___x_4553_, 1);
                        v___x_4554_ = lean_box(0);
                        v___x_4555_ = 1usize;
                        v___x_4556_ = lean_usize_add(v_i_4535_, v___x_4555_);
                        v_i_4535_ = v___x_4556_;
                        v_b_4536_ = v___x_4554_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_ref_4532_);
                        lean_dec_ref(v_a_4531_);
                        lean_dec(v_a_4530_);
                        return v___x_4553_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8___boxed(
    mut v_a_4558_: *mut LeanObject,
    mut v_a_4559_: *mut LeanObject,
    mut v_ref_4560_: *mut LeanObject,
    mut v_as_4561_: *mut LeanObject,
    mut v_sz_4562_: *mut LeanObject,
    mut v_i_4563_: *mut LeanObject,
    mut v_b_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
    mut v___y_4566_: *mut LeanObject,
    mut v___y_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
    mut v___y_4569_: *mut LeanObject,
    mut v___y_4570_: *mut LeanObject,
    mut v___y_4571_: *mut LeanObject,
    mut v___y_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4574_: usize = 0;
    let mut v_i_boxed_4575_: usize = 0;
    let mut v_res_4576_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4574_ = lean_unbox_usize(v_sz_4562_);
    lean_dec(v_sz_4562_);
    v_i_boxed_4575_ = lean_unbox_usize(v_i_4563_);
    lean_dec(v_i_4563_);
    v_res_4576_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8(v_a_4558_, v_a_4559_, v_ref_4560_, v_as_4561_, v_sz_boxed_4574_, v_i_boxed_4575_, v_b_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
    lean_dec(v___y_4572_);
    lean_dec_ref(v___y_4571_);
    lean_dec(v___y_4570_);
    lean_dec_ref(v___y_4569_);
    lean_dec(v___y_4568_);
    lean_dec_ref(v___y_4567_);
    lean_dec(v___y_4566_);
    lean_dec_ref(v___y_4565_);
    lean_dec_ref(v_as_4561_);
    return v_res_4576_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0(
    mut v___y_4584_: u8,
    mut v_suppressElabErrors_4585_: u8,
    mut v_x_4586_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_4586_) == 1 {
        let mut v_pre_4587_: *mut LeanObject = core::ptr::null_mut();
        v_pre_4587_ = lean_ctor_get(v_x_4586_, 0);
        match lean_obj_tag(v_pre_4587_) {
            1 => {
                let mut v_pre_4588_: *mut LeanObject = core::ptr::null_mut();
                v_pre_4588_ = lean_ctor_get(v_pre_4587_, 0);
                match lean_obj_tag(v_pre_4588_) {
                    0 => {
                        let mut v_str_4589_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_4590_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4591_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4592_: u8 = 0;
                        v_str_4589_ = lean_ctor_get(v_x_4586_, 1);
                        v_str_4590_ = lean_ctor_get(v_pre_4587_, 1);
                        v___x_4591_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__0;
                        v___x_4592_ = lean_string_dec_eq(v_str_4590_, v___x_4591_);
                        if v___x_4592_ == 0 {
                            let mut v___x_4593_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4594_: u8 = 0;
                            v___x_4593_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr___closed__3;
                            v___x_4594_ = lean_string_dec_eq(v_str_4590_, v___x_4593_);
                            if v___x_4594_ == 0 {
                                return v___y_4584_;
                            } else {
                                let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_4597_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_4599_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_4599_ = lean_ctor_get(v_pre_4588_, 0);
                        if lean_obj_tag(v_pre_4599_) == 0 {
                            let mut v_str_4600_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4601_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_4602_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_4604_: u8 = 0;
                            v_str_4600_ = lean_ctor_get(v_x_4586_, 1);
                            v_str_4601_ = lean_ctor_get(v_pre_4587_, 1);
                            v_str_4602_ = lean_ctor_get(v_pre_4588_, 1);
                            v___x_4603_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__3;
                            v___x_4604_ = lean_string_dec_eq(v_str_4602_, v___x_4603_);
                            if v___x_4604_ == 0 {
                                return v___y_4584_;
                            } else {
                                let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_4606_: u8 = 0;
                                v___x_4605_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___closed__4;
                                v___x_4606_ = lean_string_dec_eq(v_str_4601_, v___x_4605_);
                                if v___x_4606_ == 0 {
                                    return v___y_4584_;
                                } else {
                                    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_4609_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4610_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4611_: u8 = 0;
                v_str_4609_ = lean_ctor_get(v_x_4586_, 1);
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
    mut v___y_4612_: *mut LeanObject,
    mut v_suppressElabErrors_4613_: *mut LeanObject,
    mut v_x_4614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_20920__boxed_4615_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4616_: u8 = 0;
    let mut v_res_4617_: u8 = 0;
    let mut v_r_4618_: *mut LeanObject = core::ptr::null_mut();
    v___y_20920__boxed_4615_ = (lean_unbox(v___y_4612_) as u8);
    v_suppressElabErrors_boxed_4616_ = (lean_unbox(v_suppressElabErrors_4613_) as u8);
    v_res_4617_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0(v___y_20920__boxed_4615_, v_suppressElabErrors_boxed_4616_, v_x_4614_);
    lean_dec(v_x_4614_);
    v_r_4618_ = lean_box((v_res_4617_) as usize);
    return v_r_4618_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(
    mut v_ref_4620_: *mut LeanObject,
    mut v_msgData_4621_: *mut LeanObject,
    mut v_severity_4622_: u8,
    mut v_isSilent_4623_: u8,
    mut v___y_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4630_: u8 = 0;
    let mut v___y_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4632_: u8 = 0;
    let mut v___y_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4653_: u8 = 0;
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v___y_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4667_: u8 = 0;
    let mut v___y_4668_: u8 = 0;
    let mut v___y_4669_: u8 = 0;
    let mut v___y_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4679_: u8 = 0;
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: u8 = 0;
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v___y_4691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4692_: u8 = 0;
    let mut v___y_4693_: u8 = 0;
    let mut v___y_4694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4695_: u8 = 0;
    let mut v___y_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4704_: u8 = 0;
    let mut v___y_4705_: u8 = 0;
    let mut v___y_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4708_: u8 = 0;
    let mut v_ref_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: u8 = 0;
    let mut v___y_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4717_: u8 = 0;
    let mut v___y_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4720_: u8 = 0;
    let mut v___y_4721_: u8 = 0;
    let mut v___y_4723_: u8 = 0;
    let mut v_fileName_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4728_: u8 = 0;
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: u8 = 0;
    let mut v___x_4733_: u8 = 0;
    let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_4621_);
                    v___x_4739_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4621_);
                    v___y_4723_ = v___x_4739_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4639_ = lean_st_ref_take(v___y_4638_);
                v_currNamespace_4640_ = lean_ctor_get(v___y_4637_, 6);
                v_openDecls_4641_ = lean_ctor_get(v___y_4637_, 7);
                v_env_4642_ = lean_ctor_get(v___x_4639_, 0);
                v_nextMacroScope_4643_ = lean_ctor_get(v___x_4639_, 1);
                v_ngen_4644_ = lean_ctor_get(v___x_4639_, 2);
                v_auxDeclNGen_4645_ = lean_ctor_get(v___x_4639_, 3);
                v_traceState_4646_ = lean_ctor_get(v___x_4639_, 4);
                v_cache_4647_ = lean_ctor_get(v___x_4639_, 5);
                v_messages_4648_ = lean_ctor_get(v___x_4639_, 6);
                v_infoState_4649_ = lean_ctor_get(v___x_4639_, 7);
                v_snapshotTasks_4650_ = lean_ctor_get(v___x_4639_, 8);
                v_isSharedCheck_4664_ = (!lean_is_exclusive(v___x_4639_)) as u8;
                if v_isSharedCheck_4664_ == 0 {
                    v___x_4652_ = v___x_4639_;
                    v_isShared_4653_ = v_isSharedCheck_4664_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4650_);
                    lean_inc(v_infoState_4649_);
                    lean_inc(v_messages_4648_);
                    lean_inc(v_cache_4647_);
                    lean_inc(v_traceState_4646_);
                    lean_inc(v_auxDeclNGen_4645_);
                    lean_inc(v_ngen_4644_);
                    lean_inc(v_nextMacroScope_4643_);
                    lean_inc(v_env_4642_);
                    lean_dec(v___x_4639_);
                    v___x_4652_ = lean_box(0);
                    v_isShared_4653_ = v_isSharedCheck_4664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_4641_);
                lean_inc(v_currNamespace_4640_);
                v___x_4654_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4654_, 0, v_currNamespace_4640_);
                lean_ctor_set(v___x_4654_, 1, v_openDecls_4641_);
                v___x_4655_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_4655_, 0, v___x_4654_);
                lean_ctor_set(v___x_4655_, 1, v___y_4635_);
                lean_inc_ref(v___y_4633_);
                lean_inc_ref(v___y_4634_);
                v___x_4656_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_4656_, 0, v___y_4634_);
                lean_ctor_set(v___x_4656_, 1, v___y_4636_);
                lean_ctor_set(v___x_4656_, 2, v___y_4631_);
                lean_ctor_set(v___x_4656_, 3, v___y_4633_);
                lean_ctor_set(v___x_4656_, 4, v___x_4655_);
                lean_ctor_set_uint8(
                    v___x_4656_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_4630_,
                );
                lean_ctor_set_uint8(
                    v___x_4656_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_4632_,
                );
                lean_ctor_set_uint8(
                    v___x_4656_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4623_,
                );
                v___x_4657_ = l_Lean_MessageLog_add(v___x_4656_, v_messages_4648_);
                if v_isShared_4653_ == 0 {
                    lean_ctor_set(v___x_4652_, 6, v___x_4657_);
                    v___x_4659_ = v___x_4652_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4663_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_env_4642_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 1, v_nextMacroScope_4643_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 2, v_ngen_4644_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 3, v_auxDeclNGen_4645_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 4, v_traceState_4646_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 5, v_cache_4647_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 6, v___x_4657_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 7, v_infoState_4649_);
                    lean_ctor_set(v_reuseFailAlloc_4663_, 8, v_snapshotTasks_4650_);
                    v___x_4659_ = v_reuseFailAlloc_4663_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4660_ = lean_st_ref_set(v___y_4638_, v___x_4659_);
                v___x_4661_ = lean_box(0);
                v___x_4662_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4662_, 0, v___x_4661_);
                return v___x_4662_;
            }
            4 => {
                v___x_4674_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4621_,
                    );
                v___x_4675_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v___x_4674_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_);
                v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
                v_isSharedCheck_4689_ = (!lean_is_exclusive(v___x_4675_)) as u8;
                if v_isSharedCheck_4689_ == 0 {
                    v___x_4678_ = v___x_4675_;
                    v_isShared_4679_ = v_isSharedCheck_4689_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_4676_);
                    lean_dec(v___x_4675_);
                    v___x_4678_ = lean_box(0);
                    v_isShared_4679_ = v_isSharedCheck_4689_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_4671_, 2);
                v___x_4680_ = l_Lean_FileMap_toPosition(v___y_4671_, v___y_4672_);
                lean_dec(v___y_4672_);
                v___x_4681_ = l_Lean_FileMap_toPosition(v___y_4671_, v___y_4673_);
                lean_dec(v___y_4673_);
                v___x_4682_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4682_, 0, v___x_4681_);
                v___x_4683_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0;
                if v___y_4668_ == 0 {
                    lean_del_object(v___x_4678_);
                    lean_dec_ref(v___y_4666_);
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
                    lean_inc(v_a_4676_);
                    v___x_4684_ = l_Lean_MessageData_hasTag(v___y_4666_, v_a_4676_);
                    if v___x_4684_ == 0 {
                        lean_dec_ref_known(v___x_4682_, 1);
                        lean_dec_ref(v___x_4680_);
                        lean_dec(v_a_4676_);
                        v___x_4685_ = lean_box(0);
                        if v_isShared_4679_ == 0 {
                            lean_ctor_set(v___x_4678_, 0, v___x_4685_);
                            v___x_4687_ = v___x_4678_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4688_, 0, v___x_4685_);
                            v___x_4687_ = v_reuseFailAlloc_4688_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4678_);
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
                lean_dec(v___y_4694_);
                if lean_obj_tag(v___x_4699_) == 0 {
                    lean_inc(v___y_4698_);
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
                    v_val_4700_ = lean_ctor_get(v___x_4699_, 0);
                    lean_inc(v_val_4700_);
                    lean_dec_ref_known(v___x_4699_, 1);
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
                if lean_obj_tag(v___x_4710_) == 0 {
                    v___x_4711_ = lean_unsigned_to_nat(0);
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
                    v_val_4712_ = lean_ctor_get(v___x_4710_, 0);
                    lean_inc(v_val_4712_);
                    lean_dec_ref_known(v___x_4710_, 1);
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
                    v_fileName_4724_ = lean_ctor_get(v___y_4626_, 0);
                    v_fileMap_4725_ = lean_ctor_get(v___y_4626_, 1);
                    v_options_4726_ = lean_ctor_get(v___y_4626_, 2);
                    v_ref_4727_ = lean_ctor_get(v___y_4626_, 5);
                    v_suppressElabErrors_4728_ = lean_ctor_get_uint8(
                        v___y_4626_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4729_ = lean_box((v___y_4723_) as usize);
                    v___x_4730_ = lean_box((v_suppressElabErrors_4728_) as usize);
                    v___f_4731_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_4731_, 0, v___x_4729_);
                    lean_closure_set(v___f_4731_, 1, v___x_4730_);
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
                    lean_dec_ref(v_msgData_4621_);
                    v___x_4736_ = lean_box(0);
                    v___x_4737_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4737_, 0, v___x_4736_);
                    return v___x_4737_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___boxed(
    mut v_ref_4740_: *mut LeanObject,
    mut v_msgData_4741_: *mut LeanObject,
    mut v_severity_4742_: *mut LeanObject,
    mut v_isSilent_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
    mut v___y_4745_: *mut LeanObject,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4749_: u8 = 0;
    let mut v_isSilent_boxed_4750_: u8 = 0;
    let mut v_res_4751_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4749_ = (lean_unbox(v_severity_4742_) as u8);
    v_isSilent_boxed_4750_ = (lean_unbox(v_isSilent_4743_) as u8);
    v_res_4751_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(v_ref_4740_, v_msgData_4741_, v_severity_boxed_4749_, v_isSilent_boxed_4750_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
    lean_dec(v___y_4747_);
    lean_dec_ref(v___y_4746_);
    lean_dec(v___y_4745_);
    lean_dec_ref(v___y_4744_);
    lean_dec(v_ref_4740_);
    return v_res_4751_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9(
    mut v_msgData_4752_: *mut LeanObject,
    mut v_severity_4753_: u8,
    mut v_isSilent_4754_: u8,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
    mut v___y_4758_: *mut LeanObject,
    mut v___y_4759_: *mut LeanObject,
    mut v___y_4760_: *mut LeanObject,
    mut v___y_4761_: *mut LeanObject,
    mut v___y_4762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut LeanObject = core::ptr::null_mut();
    v_ref_4764_ = lean_ctor_get(v___y_4761_, 5);
    v___x_4765_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(v_ref_4764_, v_msgData_4752_, v_severity_4753_, v_isSilent_4754_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
    return v___x_4765_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9___boxed(
    mut v_msgData_4766_: *mut LeanObject,
    mut v_severity_4767_: *mut LeanObject,
    mut v_isSilent_4768_: *mut LeanObject,
    mut v___y_4769_: *mut LeanObject,
    mut v___y_4770_: *mut LeanObject,
    mut v___y_4771_: *mut LeanObject,
    mut v___y_4772_: *mut LeanObject,
    mut v___y_4773_: *mut LeanObject,
    mut v___y_4774_: *mut LeanObject,
    mut v___y_4775_: *mut LeanObject,
    mut v___y_4776_: *mut LeanObject,
    mut v___y_4777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_4778_: u8 = 0;
    let mut v_isSilent_boxed_4779_: u8 = 0;
    let mut v_res_4780_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_4778_ = (lean_unbox(v_severity_4767_) as u8);
    v_isSilent_boxed_4779_ = (lean_unbox(v_isSilent_4768_) as u8);
    v_res_4780_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9(v_msgData_4766_, v_severity_boxed_4778_, v_isSilent_boxed_4779_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
    lean_dec(v___y_4776_);
    lean_dec_ref(v___y_4775_);
    lean_dec(v___y_4774_);
    lean_dec_ref(v___y_4773_);
    lean_dec(v___y_4772_);
    lean_dec_ref(v___y_4771_);
    lean_dec(v___y_4770_);
    lean_dec_ref(v___y_4769_);
    return v_res_4780_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9(
    mut v_msgData_4781_: *mut LeanObject,
    mut v___y_4782_: *mut LeanObject,
    mut v___y_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
    mut v___y_4785_: *mut LeanObject,
    mut v___y_4786_: *mut LeanObject,
    mut v___y_4787_: *mut LeanObject,
    mut v___y_4788_: *mut LeanObject,
    mut v___y_4789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4792_: u8 = 0;
    let mut v___x_4793_: *mut LeanObject = core::ptr::null_mut();
    v___x_4791_ = 2;
    v___x_4792_ = 0;
    v___x_4793_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9(v_msgData_4781_, v___x_4791_, v___x_4792_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_);
    return v___x_4793_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9___boxed(
    mut v_msgData_4794_: *mut LeanObject,
    mut v___y_4795_: *mut LeanObject,
    mut v___y_4796_: *mut LeanObject,
    mut v___y_4797_: *mut LeanObject,
    mut v___y_4798_: *mut LeanObject,
    mut v___y_4799_: *mut LeanObject,
    mut v___y_4800_: *mut LeanObject,
    mut v___y_4801_: *mut LeanObject,
    mut v___y_4802_: *mut LeanObject,
    mut v___y_4803_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4804_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4802_);
    lean_dec_ref(v___y_4801_);
    lean_dec(v___y_4800_);
    lean_dec_ref(v___y_4799_);
    lean_dec(v___y_4798_);
    lean_dec_ref(v___y_4797_);
    lean_dec(v___y_4796_);
    lean_dec_ref(v___y_4795_);
    return v_res_4804_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__3(
    mut v_a_4805_: *mut LeanObject,
    mut v_a_4806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4812_: u8 = 0;
    let mut v___x_4813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4805_) == 0 {
                    v___x_4807_ = l_List_reverse___redArg(v_a_4806_);
                    return v___x_4807_;
                } else {
                    v_head_4808_ = lean_ctor_get(v_a_4805_, 0);
                    v_tail_4809_ = lean_ctor_get(v_a_4805_, 1);
                    v_isSharedCheck_4818_ = (!lean_is_exclusive(v_a_4805_)) as u8;
                    if v_isSharedCheck_4818_ == 0 {
                        v___x_4811_ = v_a_4805_;
                        v_isShared_4812_ = v_isSharedCheck_4818_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4809_);
                        lean_inc(v_head_4808_);
                        lean_dec(v_a_4805_);
                        v___x_4811_ = lean_box(0);
                        v_isShared_4812_ = v_isSharedCheck_4818_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4813_ = l_Lean_Expr_fvar___override(v_head_4808_);
                if v_isShared_4812_ == 0 {
                    lean_ctor_set(v___x_4811_, 1, v_a_4806_);
                    lean_ctor_set(v___x_4811_, 0, v___x_4813_);
                    v___x_4815_ = v___x_4811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4813_);
                    lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_a_4806_);
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
    mut v_bs_4821_: *mut LeanObject,
    mut v___y_4822_: *mut LeanObject,
    mut v___y_4823_: *mut LeanObject,
    mut v___y_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
    mut v___y_4827_: *mut LeanObject,
    mut v___y_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4831_: u8 = 0;
    let mut v___x_4832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: usize = 0;
    let mut v___x_4839_: usize = 0;
    let mut v___x_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4845_: u8 = 0;
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4831_ = lean_usize_dec_lt(v_i_4820_, v_sz_4819_);
                if v___x_4831_ == 0 {
                    v___x_4832_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4832_, 0, v_bs_4821_);
                    return v___x_4832_;
                } else {
                    v_v_4833_ = lean_array_uget_borrowed(v_bs_4821_, v_i_4820_);
                    lean_inc(v_v_4833_);
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
                    if lean_obj_tag(v___x_4834_) == 0 {
                        v_a_4835_ = lean_ctor_get(v___x_4834_, 0);
                        lean_inc(v_a_4835_);
                        lean_dec_ref_known(v___x_4834_, 1);
                        v___x_4836_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4837_ = lean_array_uset(v_bs_4821_, v_i_4820_, v___x_4836_);
                        v___x_4838_ = 1usize;
                        v___x_4839_ = lean_usize_add(v_i_4820_, v___x_4838_);
                        v___x_4840_ = lean_array_uset(v_bs_x27_4837_, v_i_4820_, v_a_4835_);
                        v_i_4820_ = v___x_4839_;
                        v_bs_4821_ = v___x_4840_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_4821_);
                        v_a_4842_ = lean_ctor_get(v___x_4834_, 0);
                        v_isSharedCheck_4849_ = (!lean_is_exclusive(v___x_4834_)) as u8;
                        if v_isSharedCheck_4849_ == 0 {
                            v___x_4844_ = v___x_4834_;
                            v_isShared_4845_ = v_isSharedCheck_4849_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4842_);
                            lean_dec(v___x_4834_);
                            v___x_4844_ = lean_box(0);
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
                    v_reuseFailAlloc_4848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4842_);
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
    mut v_sz_4850_: *mut LeanObject,
    mut v_i_4851_: *mut LeanObject,
    mut v_bs_4852_: *mut LeanObject,
    mut v___y_4853_: *mut LeanObject,
    mut v___y_4854_: *mut LeanObject,
    mut v___y_4855_: *mut LeanObject,
    mut v___y_4856_: *mut LeanObject,
    mut v___y_4857_: *mut LeanObject,
    mut v___y_4858_: *mut LeanObject,
    mut v___y_4859_: *mut LeanObject,
    mut v___y_4860_: *mut LeanObject,
    mut v___y_4861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4862_: usize = 0;
    let mut v_i_boxed_4863_: usize = 0;
    let mut v_res_4864_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4862_ = lean_unbox_usize(v_sz_4850_);
    lean_dec(v_sz_4850_);
    v_i_boxed_4863_ = lean_unbox_usize(v_i_4851_);
    lean_dec(v_i_4851_);
    v_res_4864_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__2(v_sz_boxed_4862_, v_i_boxed_4863_, v_bs_4852_, v___y_4853_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_, v___y_4860_);
    lean_dec(v___y_4860_);
    lean_dec_ref(v___y_4859_);
    lean_dec(v___y_4858_);
    lean_dec_ref(v___y_4857_);
    lean_dec(v___y_4856_);
    lean_dec_ref(v___y_4855_);
    lean_dec(v___y_4854_);
    lean_dec_ref(v___y_4853_);
    return v_res_4864_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___lam__0(
    mut v___x_4865_: *mut LeanObject,
    mut v___y_4866_: *mut LeanObject,
    mut v___y_4867_: *mut LeanObject,
    mut v___y_4868_: *mut LeanObject,
    mut v___y_4869_: *mut LeanObject,
    mut v___y_4870_: *mut LeanObject,
    mut v___y_4871_: *mut LeanObject,
    mut v___y_4872_: *mut LeanObject,
    mut v___y_4873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4879_: u8 = 0;
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4884_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4875_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(v___x_4865_, v___y_4871_);
                if lean_obj_tag(v___x_4875_) == 0 {
                    v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
                    v_isSharedCheck_4884_ = (!lean_is_exclusive(v___x_4875_)) as u8;
                    if v_isSharedCheck_4884_ == 0 {
                        v___x_4878_ = v___x_4875_;
                        v_isShared_4879_ = v_isSharedCheck_4884_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4876_);
                        lean_dec(v___x_4875_);
                        v___x_4878_ = lean_box(0);
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
                    lean_ctor_set(v___x_4878_, 0, v___x_4880_);
                    v___x_4882_ = v___x_4878_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4883_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4880_);
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
    mut v___x_4885_: *mut LeanObject,
    mut v___y_4886_: *mut LeanObject,
    mut v___y_4887_: *mut LeanObject,
    mut v___y_4888_: *mut LeanObject,
    mut v___y_4889_: *mut LeanObject,
    mut v___y_4890_: *mut LeanObject,
    mut v___y_4891_: *mut LeanObject,
    mut v___y_4892_: *mut LeanObject,
    mut v___y_4893_: *mut LeanObject,
    mut v___y_4894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4895_: *mut LeanObject = core::ptr::null_mut();
    v_res_4895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___lam__0(v___x_4885_, v___y_4886_, v___y_4887_, v___y_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
    lean_dec(v___y_4893_);
    lean_dec_ref(v___y_4892_);
    lean_dec(v___y_4891_);
    lean_dec_ref(v___y_4890_);
    lean_dec(v___y_4889_);
    lean_dec_ref(v___y_4888_);
    lean_dec(v___y_4887_);
    lean_dec_ref(v___y_4886_);
    return v_res_4895_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10(
    mut v_a_4896_: *mut LeanObject,
    mut v_sz_4897_: usize,
    mut v_i_4898_: usize,
    mut v_bs_4899_: *mut LeanObject,
    mut v___y_4900_: *mut LeanObject,
    mut v___y_4901_: *mut LeanObject,
    mut v___y_4902_: *mut LeanObject,
    mut v___y_4903_: *mut LeanObject,
    mut v___y_4904_: *mut LeanObject,
    mut v___y_4905_: *mut LeanObject,
    mut v___y_4906_: *mut LeanObject,
    mut v___y_4907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4909_: u8 = 0;
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: usize = 0;
    let mut v___x_4920_: usize = 0;
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4926_: u8 = 0;
    let mut v___x_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4909_ = lean_usize_dec_lt(v_i_4898_, v_sz_4897_);
                if v___x_4909_ == 0 {
                    lean_dec(v_a_4896_);
                    v___x_4910_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4910_, 0, v_bs_4899_);
                    return v___x_4910_;
                } else {
                    v_v_4911_ = lean_array_uget_borrowed(v_bs_4899_, v_i_4898_);
                    v_snd_4912_ = lean_ctor_get(v_v_4911_, 1);
                    lean_inc(v_a_4896_);
                    v___x_4913_ = l_Lean_mkMVar(v_a_4896_);
                    v___f_4914_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10___lam__0___boxed as *mut core::ffi::c_void, 10, 1);
                    lean_closure_set(v___f_4914_, 0, v___x_4913_);
                    lean_inc(v_snd_4912_);
                    v___x_4915_ = l_Lean_Meta_withMCtx___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__1___redArg(v_snd_4912_, v___f_4914_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, v___y_4907_);
                    if lean_obj_tag(v___x_4915_) == 0 {
                        v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
                        lean_inc(v_a_4916_);
                        lean_dec_ref_known(v___x_4915_, 1);
                        v___x_4917_ = lean_unsigned_to_nat(0);
                        v_bs_x27_4918_ = lean_array_uset(v_bs_4899_, v_i_4898_, v___x_4917_);
                        v___x_4919_ = 1usize;
                        v___x_4920_ = lean_usize_add(v_i_4898_, v___x_4919_);
                        v___x_4921_ = lean_array_uset(v_bs_x27_4918_, v_i_4898_, v_a_4916_);
                        v_i_4898_ = v___x_4920_;
                        v_bs_4899_ = v___x_4921_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_4899_);
                        lean_dec(v_a_4896_);
                        v_a_4923_ = lean_ctor_get(v___x_4915_, 0);
                        v_isSharedCheck_4930_ = (!lean_is_exclusive(v___x_4915_)) as u8;
                        if v_isSharedCheck_4930_ == 0 {
                            v___x_4925_ = v___x_4915_;
                            v_isShared_4926_ = v_isSharedCheck_4930_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4923_);
                            lean_dec(v___x_4915_);
                            v___x_4925_ = lean_box(0);
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
                    v_reuseFailAlloc_4929_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4923_);
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
    mut v_a_4931_: *mut LeanObject,
    mut v_sz_4932_: *mut LeanObject,
    mut v_i_4933_: *mut LeanObject,
    mut v_bs_4934_: *mut LeanObject,
    mut v___y_4935_: *mut LeanObject,
    mut v___y_4936_: *mut LeanObject,
    mut v___y_4937_: *mut LeanObject,
    mut v___y_4938_: *mut LeanObject,
    mut v___y_4939_: *mut LeanObject,
    mut v___y_4940_: *mut LeanObject,
    mut v___y_4941_: *mut LeanObject,
    mut v___y_4942_: *mut LeanObject,
    mut v___y_4943_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4944_: usize = 0;
    let mut v_i_boxed_4945_: usize = 0;
    let mut v_res_4946_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4944_ = lean_unbox_usize(v_sz_4932_);
    lean_dec(v_sz_4932_);
    v_i_boxed_4945_ = lean_unbox_usize(v_i_4933_);
    lean_dec(v_i_4933_);
    v_res_4946_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10(v_a_4931_, v_sz_boxed_4944_, v_i_boxed_4945_, v_bs_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
    lean_dec(v___y_4942_);
    lean_dec_ref(v___y_4941_);
    lean_dec(v___y_4940_);
    lean_dec_ref(v___y_4939_);
    lean_dec(v___y_4938_);
    lean_dec_ref(v___y_4937_);
    lean_dec(v___y_4936_);
    lean_dec_ref(v___y_4935_);
    return v_res_4946_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__4() -> *mut LeanObject {
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    v___x_4954_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__3;
    v___x_4955_ = l_Lean_MessageData_ofFormat(v___x_4954_);
    return v___x_4955_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8() -> *mut LeanObject {
    let mut v___x_4960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut LeanObject = core::ptr::null_mut();
    v___x_4960_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__7;
    v___x_4961_ = l_Lean_stringToMessageData(v___x_4960_);
    return v___x_4961_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f___lam__2(
    mut v___y_4963_: *mut LeanObject,
    mut v_config_4964_: *mut LeanObject,
    mut v_snd_4965_: *mut LeanObject,
    mut v_a_4966_: *mut LeanObject,
    mut v_a_4967_: *mut LeanObject,
    mut v_ref_4968_: *mut LeanObject,
    mut v_requireClose_4969_: u8,
    mut v___y_4970_: *mut LeanObject,
    mut v___y_4971_: *mut LeanObject,
    mut v___y_4972_: *mut LeanObject,
    mut v___y_4973_: *mut LeanObject,
    mut v___y_4974_: *mut LeanObject,
    mut v___y_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: u8 = 0;
    let mut v___x_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4986_: usize = 0;
    let mut v___x_4987_: usize = 0;
    let mut v___x_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_grind_4990_: u8 = 0;
    let mut v_try_x3f_4991_: u8 = 0;
    let mut v_star_4992_: u8 = 0;
    let mut v_all_4993_: u8 = 0;
    let mut v___x_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5009_: u8 = 0;
    let mut v___x_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: u8 = 0;
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut v_val_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5021_: u8 = 0;
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5024_: usize = 0;
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5030_: u8 = 0;
    let mut v___y_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5041_: usize = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: u8 = 0;
    let mut v___x_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5059_: usize = 0;
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: u8 = 0;
    let mut v___x_5065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5073_: u8 = 0;
    let mut v___x_5075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5077_: u8 = 0;
    let mut v___y_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: u8 = 0;
    let mut v___x_5105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: u8 = 0;
    let mut v___x_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: u8 = 0;
    let mut v___x_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5119_: u8 = 0;
    let mut v_isSharedCheck_5120_: u8 = 0;
    let mut v_a_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5124_: u8 = 0;
    let mut v___x_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5128_: u8 = 0;
    let mut v_a_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5132_: u8 = 0;
    let mut v___x_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4986_ = lean_array_size(v___y_4963_);
                v___x_4987_ = 0usize;
                v___x_4988_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__2(v_sz_4986_, v___x_4987_, v___y_4963_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
                if lean_obj_tag(v___x_4988_) == 0 {
                    v_a_4989_ = lean_ctor_get(v___x_4988_, 0);
                    lean_inc(v_a_4989_);
                    lean_dec_ref_known(v___x_4988_, 1);
                    v_grind_4990_ = lean_ctor_get_uint8(v_config_4964_, 0 as u32);
                    v_try_x3f_4991_ = lean_ctor_get_uint8(v_config_4964_, 1 as u32);
                    v_star_4992_ = lean_ctor_get_uint8(v_config_4964_, 2 as u32);
                    v_all_4993_ = lean_ctor_get_uint8(v_config_4964_, 3 as u32);
                    v___x_4994_ = lean_array_to_list(v_a_4989_);
                    v___x_4995_ = lean_box(0);
                    v___x_4996_ =
                        l_List_mapTR_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__3(
                            v___x_4994_,
                            v___x_4995_,
                        );
                    v___x_4997_ = lean_box((v_grind_4990_) as usize);
                    v___x_4998_ = lean_box((v_try_x3f_4991_) as usize);
                    lean_inc(v___x_4996_);
                    v___f_4999_ = lean_alloc_closure(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        3,
                    );
                    lean_closure_set(v___f_4999_, 0, v___x_4996_);
                    lean_closure_set(v___f_4999_, 1, v___x_4997_);
                    lean_closure_set(v___f_4999_, 2, v___x_4998_);
                    v___f_5000_ = lean_alloc_closure(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        1,
                    );
                    lean_closure_set(v___f_5000_, 0, v___x_4996_);
                    v___x_5001_ = lean_unsigned_to_nat(10);
                    lean_inc(v_snd_4965_);
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
                    if lean_obj_tag(v___x_5002_) == 0 {
                        v_a_5003_ = lean_ctor_get(v___x_5002_, 0);
                        lean_inc(v_a_5003_);
                        lean_dec_ref_known(v___x_5002_, 1);
                        if lean_obj_tag(v_a_5003_) == 0 {
                            lean_dec(v_snd_4965_);
                            v___x_5004_ = l_Lean_mkMVar(v_a_4966_);
                            v___x_5005_ = l_Lean_instantiateMVars___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__0___redArg(v___x_5004_, v___y_4975_);
                            v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
                            v_isSharedCheck_5017_ = (!lean_is_exclusive(v___x_5005_)) as u8;
                            if v_isSharedCheck_5017_ == 0 {
                                v___x_5008_ = v___x_5005_;
                                v_isShared_5009_ = v_isSharedCheck_5017_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_5006_);
                                lean_dec(v___x_5005_);
                                v___x_5008_ = lean_box(0);
                                v_isShared_5009_ = v_isSharedCheck_5017_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_val_5018_ = lean_ctor_get(v_a_5003_, 0);
                            v_isSharedCheck_5120_ = (!lean_is_exclusive(v_a_5003_)) as u8;
                            if v_isSharedCheck_5120_ == 0 {
                                v___x_5020_ = v_a_5003_;
                                v_isShared_5021_ = v_isSharedCheck_5120_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_val_5018_);
                                lean_dec(v_a_5003_);
                                v___x_5020_ = lean_box(0);
                                v_isShared_5021_ = v_isSharedCheck_5120_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_ref_4968_);
                        lean_dec_ref(v_a_4967_);
                        lean_dec(v_a_4966_);
                        lean_dec(v_snd_4965_);
                        v_a_5121_ = lean_ctor_get(v___x_5002_, 0);
                        v_isSharedCheck_5128_ = (!lean_is_exclusive(v___x_5002_)) as u8;
                        if v_isSharedCheck_5128_ == 0 {
                            v___x_5123_ = v___x_5002_;
                            v_isShared_5124_ = v_isSharedCheck_5128_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5121_);
                            lean_dec(v___x_5002_);
                            v___x_5123_ = lean_box(0);
                            v_isShared_5124_ = v_isSharedCheck_5128_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_ref_4968_);
                    lean_dec_ref(v_a_4967_);
                    lean_dec(v_a_4966_);
                    lean_dec(v_snd_4965_);
                    v_a_5129_ = lean_ctor_get(v___x_4988_, 0);
                    v_isSharedCheck_5136_ = (!lean_is_exclusive(v___x_4988_)) as u8;
                    if v_isSharedCheck_5136_ == 0 {
                        v___x_5131_ = v___x_4988_;
                        v_isShared_5132_ = v_isSharedCheck_5136_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5129_);
                        lean_dec(v___x_4988_);
                        v___x_5131_ = lean_box(0);
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
                v___x_5011_ = lean_box(0);
                v___x_5012_ = 0;
                if v_isShared_5009_ == 0 {
                    lean_ctor_set_tag(v___x_5008_, 1);
                    lean_ctor_set(v___x_5008_, 0, v_a_4967_);
                    v___x_5014_ = v___x_5008_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_4967_);
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
                v___x_5022_ = lean_unsigned_to_nat(0);
                v___x_5023_ = l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__1;
                v_sz_5024_ = lean_array_size(v_val_5018_);
                v___x_5025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__7(v_val_5018_, v_sz_5024_, v___x_4987_, v___x_5023_);
                v_fst_5026_ = lean_ctor_get(v___x_5025_, 0);
                v_snd_5027_ = lean_ctor_get(v___x_5025_, 1);
                v_isSharedCheck_5119_ = (!lean_is_exclusive(v___x_5025_)) as u8;
                if v_isSharedCheck_5119_ == 0 {
                    v___x_5029_ = v___x_5025_;
                    v_isShared_5030_ = v_isSharedCheck_5119_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_5027_);
                    lean_inc(v_fst_5026_);
                    lean_dec(v___x_5025_);
                    v___x_5029_ = lean_box(0);
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
                        lean_del_object(v___x_5029_);
                        lean_dec(v_snd_5027_);
                        lean_dec(v_fst_5026_);
                        lean_del_object(v___x_5020_);
                        lean_dec(v_ref_4968_);
                        lean_dec_ref(v_a_4967_);
                        lean_dec(v_a_4966_);
                        lean_dec(v_snd_4965_);
                        v___x_5115_ = lean_array_get_size(v_val_5018_);
                        lean_dec(v_val_5018_);
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
                    v___x_5040_ = lean_box(0);
                    v_sz_5041_ = lean_array_size(v_snd_5027_);
                    v___x_5042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__8(v_a_4966_, v_a_4967_, v_ref_4968_, v_snd_5027_, v_sz_5041_, v___x_4987_, v___x_5040_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_, v___y_5036_, v___y_5037_, v___y_5038_, v___y_5039_);
                    lean_dec(v_snd_5027_);
                    if lean_obj_tag(v___x_5042_) == 0 {
                        lean_dec_ref_known(v___x_5042_, 1);
                        v___x_5043_ = lean_array_get_size(v_val_5018_);
                        lean_dec(v_val_5018_);
                        v___x_5044_ = lean_nat_dec_eq(v___x_5043_, v___x_5022_);
                        if v___x_5044_ == 0 {
                            v___y_4980_ = v___y_5036_;
                            v___y_4981_ = v___y_5037_;
                            v___y_4982_ = v___y_5038_;
                            v___y_4983_ = v___y_5039_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5045_ = lean_obj_once(
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
                            if lean_obj_tag(v___x_5046_) == 0 {
                                lean_dec_ref_known(v___x_5046_, 1);
                                v___y_4980_ = v___y_5036_;
                                v___y_4981_ = v___y_5037_;
                                v___y_4982_ = v___y_5038_;
                                v___y_4983_ = v___y_5039_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v_snd_4965_);
                                return v___x_5046_;
                            }
                        }
                    } else {
                        lean_dec(v_val_5018_);
                        lean_dec(v_snd_4965_);
                        return v___x_5042_;
                    }
                } else {
                    lean_dec(v_snd_5027_);
                    lean_dec(v_val_5018_);
                    lean_dec(v_ref_4968_);
                    lean_dec_ref(v_a_4967_);
                    lean_dec(v_a_4966_);
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
                v___x_5057_ = lean_unsigned_to_nat(90);
                v___x_5058_ = l_Lean_reportOutOfHeartbeats(
                    v___x_5056_,
                    v_ref_4968_,
                    v___x_5057_,
                    v___y_5054_,
                    v___y_5055_,
                );
                if lean_obj_tag(v___x_5058_) == 0 {
                    lean_dec_ref_known(v___x_5058_, 1);
                    v_sz_5059_ = lean_array_size(v_fst_5026_);
                    lean_inc(v_a_4966_);
                    v___x_5060_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__10(v_a_4966_, v_sz_5059_, v___x_4987_, v_fst_5026_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
                    if lean_obj_tag(v___x_5060_) == 0 {
                        v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
                        lean_inc(v_a_5061_);
                        lean_dec_ref_known(v___x_5060_, 1);
                        v___x_5062_ = lean_array_get_size(v_a_5061_);
                        v___x_5063_ = lean_nat_dec_eq(v___x_5062_, v___x_5022_);
                        if v___x_5063_ == 0 {
                            v___x_5064_ = 1;
                            v___x_5065_ = lean_box(0);
                            lean_inc_ref(v_a_4967_);
                            if v_isShared_5021_ == 0 {
                                lean_ctor_set(v___x_5020_, 0, v_a_4967_);
                                v___x_5067_ = v___x_5020_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_5069_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_5069_, 0, v_a_4967_);
                                v___x_5067_ = v_reuseFailAlloc_5069_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5061_);
                            lean_del_object(v___x_5020_);
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
                        lean_dec(v_snd_5027_);
                        lean_del_object(v___x_5020_);
                        lean_dec(v_val_5018_);
                        lean_dec(v_ref_4968_);
                        lean_dec_ref(v_a_4967_);
                        lean_dec(v_a_4966_);
                        lean_dec(v_snd_4965_);
                        v_a_5070_ = lean_ctor_get(v___x_5060_, 0);
                        v_isSharedCheck_5077_ = (!lean_is_exclusive(v___x_5060_)) as u8;
                        if v_isSharedCheck_5077_ == 0 {
                            v___x_5072_ = v___x_5060_;
                            v_isShared_5073_ = v_isSharedCheck_5077_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5070_);
                            lean_dec(v___x_5060_);
                            v___x_5072_ = lean_box(0);
                            v_isShared_5073_ = v_isSharedCheck_5077_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_snd_5027_);
                    lean_dec(v_fst_5026_);
                    lean_del_object(v___x_5020_);
                    lean_dec(v_val_5018_);
                    lean_dec(v_ref_4968_);
                    lean_dec_ref(v_a_4967_);
                    lean_dec(v_a_4966_);
                    lean_dec(v_snd_4965_);
                    return v___x_5058_;
                }
            }
            8 => {
                lean_inc(v_ref_4968_);
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
                if lean_obj_tag(v___x_5068_) == 0 {
                    lean_dec_ref_known(v___x_5068_, 1);
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
                    lean_dec(v_snd_5027_);
                    lean_dec(v_val_5018_);
                    lean_dec(v_ref_4968_);
                    lean_dec_ref(v_a_4967_);
                    lean_dec(v_a_4966_);
                    lean_dec(v_snd_4965_);
                    return v___x_5068_;
                }
            }
            9 => {
                if v_isShared_5073_ == 0 {
                    v___x_5075_ = v___x_5072_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5076_, 0, v_a_5070_);
                    v___x_5075_ = v_reuseFailAlloc_5076_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5075_;
            }
            11 => {
                v___x_5088_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8_once
                    ),
                    _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8,
                );
                lean_inc_ref(v___y_5087_);
                v___x_5089_ = l_Lean_stringToMessageData(v___y_5087_);
                if v_isShared_5030_ == 0 {
                    lean_ctor_set_tag(v___x_5029_, 7);
                    lean_ctor_set(v___x_5029_, 1, v___x_5089_);
                    lean_ctor_set(v___x_5029_, 0, v___x_5088_);
                    v___x_5091_ = v___x_5029_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5093_, 0, v___x_5088_);
                    lean_ctor_set(v_reuseFailAlloc_5093_, 1, v___x_5089_);
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
                    lean_del_object(v___x_5029_);
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
                        lean_del_object(v___x_5029_);
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
                            lean_del_object(v___x_5029_);
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
                            lean_dec(v_fst_5026_);
                            lean_del_object(v___x_5020_);
                            lean_dec(v_val_5018_);
                            lean_dec(v_ref_4968_);
                            lean_dec_ref(v_a_4967_);
                            lean_dec(v_a_4966_);
                            lean_dec(v_snd_4965_);
                            v___x_5105_ = lean_array_get_size(v_snd_5027_);
                            lean_dec(v_snd_5027_);
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
                v___x_5111_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8_once
                    ),
                    _init_l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___closed__8,
                );
                lean_inc_ref(v___y_5110_);
                v___x_5112_ = l_Lean_stringToMessageData(v___y_5110_);
                v___x_5113_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5113_, 0, v___x_5111_);
                lean_ctor_set(v___x_5113_, 1, v___x_5112_);
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
                    v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
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
                    v_reuseFailAlloc_5135_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5135_, 0, v_a_5129_);
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
    mut v___y_5137_: *mut LeanObject,
    mut v_config_5138_: *mut LeanObject,
    mut v_snd_5139_: *mut LeanObject,
    mut v_a_5140_: *mut LeanObject,
    mut v_a_5141_: *mut LeanObject,
    mut v_ref_5142_: *mut LeanObject,
    mut v_requireClose_5143_: *mut LeanObject,
    mut v___y_5144_: *mut LeanObject,
    mut v___y_5145_: *mut LeanObject,
    mut v___y_5146_: *mut LeanObject,
    mut v___y_5147_: *mut LeanObject,
    mut v___y_5148_: *mut LeanObject,
    mut v___y_5149_: *mut LeanObject,
    mut v___y_5150_: *mut LeanObject,
    mut v___y_5151_: *mut LeanObject,
    mut v___y_5152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_requireClose_boxed_5153_: u8 = 0;
    let mut v_res_5154_: *mut LeanObject = core::ptr::null_mut();
    v_requireClose_boxed_5153_ = (lean_unbox(v_requireClose_5143_) as u8);
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
    lean_dec(v___y_5151_);
    lean_dec_ref(v___y_5150_);
    lean_dec(v___y_5149_);
    lean_dec_ref(v___y_5148_);
    lean_dec(v___y_5147_);
    lean_dec_ref(v___y_5146_);
    lean_dec(v___y_5145_);
    lean_dec_ref(v___y_5144_);
    lean_dec_ref(v_config_5138_);
    return v_res_5154_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_exact_x3f(
    mut v_ref_5157_: *mut LeanObject,
    mut v_config_5158_: *mut LeanObject,
    mut v_required_5159_: *mut LeanObject,
    mut v_requireClose_5160_: u8,
    mut v_a_5161_: *mut LeanObject,
    mut v_a_5162_: *mut LeanObject,
    mut v_a_5163_: *mut LeanObject,
    mut v_a_5164_: *mut LeanObject,
    mut v_a_5165_: *mut LeanObject,
    mut v_a_5166_: *mut LeanObject,
    mut v_a_5167_: *mut LeanObject,
    mut v_a_5168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5189_: u8 = 0;
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5193_: u8 = 0;
    let mut v_a_5194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5197_: u8 = 0;
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5201_: u8 = 0;
    let mut v_a_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5205_: u8 = 0;
    let mut v___x_5207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5209_: u8 = 0;
    let mut v_a_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5213_: u8 = 0;
    let mut v___x_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5170_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_5162_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_,
                );
                if lean_obj_tag(v___x_5170_) == 0 {
                    v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
                    lean_inc(v_a_5171_);
                    lean_dec_ref_known(v___x_5170_, 1);
                    v___x_5172_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v_a_5162_, v_a_5164_, v_a_5166_, v_a_5168_,
                    );
                    if lean_obj_tag(v___x_5172_) == 0 {
                        v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
                        lean_inc(v_a_5173_);
                        lean_dec_ref_known(v___x_5172_, 1);
                        v___x_5174_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                            v_a_5162_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_,
                        );
                        if lean_obj_tag(v___x_5174_) == 0 {
                            v_a_5175_ = lean_ctor_get(v___x_5174_, 0);
                            lean_inc(v_a_5175_);
                            lean_dec_ref_known(v___x_5174_, 1);
                            v___x_5176_ = l_Lean_MVarId_intros(
                                v_a_5175_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_,
                            );
                            if lean_obj_tag(v___x_5176_) == 0 {
                                v_a_5177_ = lean_ctor_get(v___x_5176_, 0);
                                lean_inc(v_a_5177_);
                                lean_dec_ref_known(v___x_5176_, 1);
                                v_snd_5178_ = lean_ctor_get(v_a_5177_, 1);
                                lean_inc(v_snd_5178_);
                                lean_dec(v_a_5177_);
                                if lean_obj_tag(v_required_5159_) == 0 {
                                    v___x_5184_ = l_Lean_Elab_LibrarySearch_exact_x3f___closed__0;
                                    v___y_5180_ = v___x_5184_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_5185_ = lean_ctor_get(v_required_5159_, 0);
                                    lean_inc(v_val_5185_);
                                    lean_dec_ref_known(v_required_5159_, 1);
                                    v___y_5180_ = v_val_5185_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5173_);
                                lean_dec(v_a_5171_);
                                lean_dec(v_required_5159_);
                                lean_dec_ref(v_config_5158_);
                                lean_dec(v_ref_5157_);
                                v_a_5186_ = lean_ctor_get(v___x_5176_, 0);
                                v_isSharedCheck_5193_ = (!lean_is_exclusive(v___x_5176_)) as u8;
                                if v_isSharedCheck_5193_ == 0 {
                                    v___x_5188_ = v___x_5176_;
                                    v_isShared_5189_ = v_isSharedCheck_5193_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_5186_);
                                    lean_dec(v___x_5176_);
                                    v___x_5188_ = lean_box(0);
                                    v_isShared_5189_ = v_isSharedCheck_5193_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5173_);
                            lean_dec(v_a_5171_);
                            lean_dec(v_required_5159_);
                            lean_dec_ref(v_config_5158_);
                            lean_dec(v_ref_5157_);
                            v_a_5194_ = lean_ctor_get(v___x_5174_, 0);
                            v_isSharedCheck_5201_ = (!lean_is_exclusive(v___x_5174_)) as u8;
                            if v_isSharedCheck_5201_ == 0 {
                                v___x_5196_ = v___x_5174_;
                                v_isShared_5197_ = v_isSharedCheck_5201_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5194_);
                                lean_dec(v___x_5174_);
                                v___x_5196_ = lean_box(0);
                                v_isShared_5197_ = v_isSharedCheck_5201_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5171_);
                        lean_dec(v_required_5159_);
                        lean_dec_ref(v_config_5158_);
                        lean_dec(v_ref_5157_);
                        v_a_5202_ = lean_ctor_get(v___x_5172_, 0);
                        v_isSharedCheck_5209_ = (!lean_is_exclusive(v___x_5172_)) as u8;
                        if v_isSharedCheck_5209_ == 0 {
                            v___x_5204_ = v___x_5172_;
                            v_isShared_5205_ = v_isSharedCheck_5209_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5202_);
                            lean_dec(v___x_5172_);
                            v___x_5204_ = lean_box(0);
                            v_isShared_5205_ = v_isSharedCheck_5209_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_required_5159_);
                    lean_dec_ref(v_config_5158_);
                    lean_dec(v_ref_5157_);
                    v_a_5210_ = lean_ctor_get(v___x_5170_, 0);
                    v_isSharedCheck_5217_ = (!lean_is_exclusive(v___x_5170_)) as u8;
                    if v_isSharedCheck_5217_ == 0 {
                        v___x_5212_ = v___x_5170_;
                        v_isShared_5213_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5210_);
                        lean_dec(v___x_5170_);
                        v___x_5212_ = lean_box(0);
                        v_isShared_5213_ = v_isSharedCheck_5217_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5181_ = lean_box((v_requireClose_5160_) as usize);
                lean_inc(v_snd_5178_);
                v___f_5182_ = lean_alloc_closure(
                    l_Lean_Elab_LibrarySearch_exact_x3f___lam__2___boxed as *mut core::ffi::c_void,
                    16,
                    7,
                );
                lean_closure_set(v___f_5182_, 0, v___y_5180_);
                lean_closure_set(v___f_5182_, 1, v_config_5158_);
                lean_closure_set(v___f_5182_, 2, v_snd_5178_);
                lean_closure_set(v___f_5182_, 3, v_a_5171_);
                lean_closure_set(v___f_5182_, 4, v_a_5173_);
                lean_closure_set(v___f_5182_, 5, v_ref_5157_);
                lean_closure_set(v___f_5182_, 6, v___x_5181_);
                v___x_5183_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__12___redArg(v_snd_5178_, v___f_5182_, v_a_5161_, v_a_5162_, v_a_5163_, v_a_5164_, v_a_5165_, v_a_5166_, v_a_5167_, v_a_5168_);
                return v___x_5183_;
            }
            2 => {
                if v_isShared_5189_ == 0 {
                    v___x_5191_ = v___x_5188_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5192_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
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
                    v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
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
                    v_reuseFailAlloc_5208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5208_, 0, v_a_5202_);
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
                    v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
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
    mut v_ref_5218_: *mut LeanObject,
    mut v_config_5219_: *mut LeanObject,
    mut v_required_5220_: *mut LeanObject,
    mut v_requireClose_5221_: *mut LeanObject,
    mut v_a_5222_: *mut LeanObject,
    mut v_a_5223_: *mut LeanObject,
    mut v_a_5224_: *mut LeanObject,
    mut v_a_5225_: *mut LeanObject,
    mut v_a_5226_: *mut LeanObject,
    mut v_a_5227_: *mut LeanObject,
    mut v_a_5228_: *mut LeanObject,
    mut v_a_5229_: *mut LeanObject,
    mut v_a_5230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_requireClose_boxed_5231_: u8 = 0;
    let mut v_res_5232_: *mut LeanObject = core::ptr::null_mut();
    v_requireClose_boxed_5231_ = (lean_unbox(v_requireClose_5221_) as u8);
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
    lean_dec(v_a_5229_);
    lean_dec_ref(v_a_5228_);
    lean_dec(v_a_5227_);
    lean_dec_ref(v_a_5226_);
    lean_dec(v_a_5225_);
    lean_dec_ref(v_a_5224_);
    lean_dec(v_a_5223_);
    lean_dec_ref(v_a_5222_);
    return v_res_5232_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__11(
    mut v_00_u03b1_5233_: *mut LeanObject,
    mut v_msg_5234_: *mut LeanObject,
    mut v___y_5235_: *mut LeanObject,
    mut v___y_5236_: *mut LeanObject,
    mut v___y_5237_: *mut LeanObject,
    mut v___y_5238_: *mut LeanObject,
    mut v___y_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
    mut v___y_5241_: *mut LeanObject,
    mut v___y_5242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_5245_: *mut LeanObject,
    mut v_msg_5246_: *mut LeanObject,
    mut v___y_5247_: *mut LeanObject,
    mut v___y_5248_: *mut LeanObject,
    mut v___y_5249_: *mut LeanObject,
    mut v___y_5250_: *mut LeanObject,
    mut v___y_5251_: *mut LeanObject,
    mut v___y_5252_: *mut LeanObject,
    mut v___y_5253_: *mut LeanObject,
    mut v___y_5254_: *mut LeanObject,
    mut v___y_5255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5256_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5254_);
    lean_dec_ref(v___y_5253_);
    lean_dec(v___y_5252_);
    lean_dec_ref(v___y_5251_);
    lean_dec(v___y_5250_);
    lean_dec_ref(v___y_5249_);
    lean_dec(v___y_5248_);
    lean_dec_ref(v___y_5247_);
    return v_res_5256_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11(
    mut v_ref_5257_: *mut LeanObject,
    mut v_msgData_5258_: *mut LeanObject,
    mut v_severity_5259_: u8,
    mut v_isSilent_5260_: u8,
    mut v___y_5261_: *mut LeanObject,
    mut v___y_5262_: *mut LeanObject,
    mut v___y_5263_: *mut LeanObject,
    mut v___y_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    v___x_5270_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg(v_ref_5257_, v_msgData_5258_, v_severity_5259_, v_isSilent_5260_, v___y_5265_, v___y_5266_, v___y_5267_, v___y_5268_);
    return v___x_5270_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___boxed(
    mut v_ref_5271_: *mut LeanObject,
    mut v_msgData_5272_: *mut LeanObject,
    mut v_severity_5273_: *mut LeanObject,
    mut v_isSilent_5274_: *mut LeanObject,
    mut v___y_5275_: *mut LeanObject,
    mut v___y_5276_: *mut LeanObject,
    mut v___y_5277_: *mut LeanObject,
    mut v___y_5278_: *mut LeanObject,
    mut v___y_5279_: *mut LeanObject,
    mut v___y_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5284_: u8 = 0;
    let mut v_isSilent_boxed_5285_: u8 = 0;
    let mut v_res_5286_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5284_ = (lean_unbox(v_severity_5273_) as u8);
    v_isSilent_boxed_5285_ = (lean_unbox(v_isSilent_5274_) as u8);
    v_res_5286_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11(v_ref_5271_, v_msgData_5272_, v_severity_boxed_5284_, v_isSilent_boxed_5285_, v___y_5275_, v___y_5276_, v___y_5277_, v___y_5278_, v___y_5279_, v___y_5280_, v___y_5281_, v___y_5282_);
    lean_dec(v___y_5282_);
    lean_dec_ref(v___y_5281_);
    lean_dec(v___y_5280_);
    lean_dec_ref(v___y_5279_);
    lean_dec(v___y_5278_);
    lean_dec_ref(v___y_5277_);
    lean_dec(v___y_5276_);
    lean_dec_ref(v___y_5275_);
    lean_dec(v_ref_5271_);
    return v_res_5286_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_5287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    v___x_5287_ = lean_box(0);
    v___x_5288_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_5289_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_5289_, 0, v___x_5288_);
    lean_ctor_set(v___x_5289_, 1, v___x_5287_);
    return v___x_5289_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    v___x_5291_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0);
    v___x_5292_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5292_, 0, v___x_5291_);
    return v___x_5292_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___boxed(
    mut v___y_5293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5294_: *mut LeanObject = core::ptr::null_mut();
    v_res_5294_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
    return v_res_5294_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0(
    mut v_00_u03b1_5295_: *mut LeanObject,
    mut v___y_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
    mut v___y_5298_: *mut LeanObject,
    mut v___y_5299_: *mut LeanObject,
    mut v___y_5300_: *mut LeanObject,
    mut v___y_5301_: *mut LeanObject,
    mut v___y_5302_: *mut LeanObject,
    mut v___y_5303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5305_: *mut LeanObject = core::ptr::null_mut();
    v___x_5305_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
    return v___x_5305_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___boxed(
    mut v_00_u03b1_5306_: *mut LeanObject,
    mut v___y_5307_: *mut LeanObject,
    mut v___y_5308_: *mut LeanObject,
    mut v___y_5309_: *mut LeanObject,
    mut v___y_5310_: *mut LeanObject,
    mut v___y_5311_: *mut LeanObject,
    mut v___y_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5316_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5314_);
    lean_dec_ref(v___y_5313_);
    lean_dec(v___y_5312_);
    lean_dec_ref(v___y_5311_);
    lean_dec(v___y_5310_);
    lean_dec_ref(v___y_5309_);
    lean_dec(v___y_5308_);
    lean_dec_ref(v___y_5307_);
    return v_res_5316_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__1(
    mut v_sz_5317_: usize,
    mut v_i_5318_: usize,
    mut v_bs_5319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5320_: u8 = 0;
    let mut v_v_5321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: usize = 0;
    let mut v___x_5325_: usize = 0;
    let mut v___x_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5320_ = lean_usize_dec_lt(v_i_5318_, v_sz_5317_);
                if v___x_5320_ == 0 {
                    return v_bs_5319_;
                } else {
                    v_v_5321_ = lean_array_uget(v_bs_5319_, v_i_5318_);
                    v___x_5322_ = lean_unsigned_to_nat(0);
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
    mut v_sz_5328_: *mut LeanObject,
    mut v_i_5329_: *mut LeanObject,
    mut v_bs_5330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5331_: usize = 0;
    let mut v_i_boxed_5332_: usize = 0;
    let mut v_res_5333_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5331_ = lean_unbox_usize(v_sz_5328_);
    lean_dec(v_sz_5328_);
    v_i_boxed_5332_ = lean_unbox_usize(v_i_5329_);
    lean_dec(v_i_5329_);
    v_res_5333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__1(v_sz_boxed_5331_, v_i_boxed_5332_, v_bs_5330_);
    return v_res_5333_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__2(
    mut v_sz_5334_: usize,
    mut v_i_5335_: usize,
    mut v_bs_5336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5337_: u8 = 0;
    let mut v___x_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: usize = 0;
    let mut v___x_5343_: usize = 0;
    let mut v___x_5344_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5337_ = lean_usize_dec_lt(v_i_5335_, v_sz_5334_);
                if v___x_5337_ == 0 {
                    v___x_5338_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5338_, 0, v_bs_5336_);
                    return v___x_5338_;
                } else {
                    v_v_5339_ = lean_array_uget(v_bs_5336_, v_i_5335_);
                    v___x_5340_ = lean_unsigned_to_nat(0);
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
    mut v_sz_5346_: *mut LeanObject,
    mut v_i_5347_: *mut LeanObject,
    mut v_bs_5348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5349_: usize = 0;
    let mut v_i_boxed_5350_: usize = 0;
    let mut v_res_5351_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5349_ = lean_unbox_usize(v_sz_5346_);
    lean_dec(v_sz_5346_);
    v_i_boxed_5350_ = lean_unbox_usize(v_i_5347_);
    lean_dec(v_i_5347_);
    v_res_5351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalExact_spec__2(v_sz_boxed_5349_, v_i_boxed_5350_, v_bs_5348_);
    return v_res_5351_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(
    mut v___x_5352_: u8,
    mut v___x_5353_: u8,
    mut v_as_5354_: *mut LeanObject,
    mut v_i_5355_: usize,
    mut v_stop_5356_: usize,
    mut v_b_5357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5363_: u8 = 0;
    let mut v_fst_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: u8 = 0;
    let mut v_snd_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v___x_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_unused_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5379_: u8 = 0;
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5386_: u8 = 0;
    let mut v_unused_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5363_ = lean_usize_dec_eq(v_i_5355_, v_stop_5356_);
                if v___x_5363_ == 0 {
                    v_fst_5364_ = lean_ctor_get(v_b_5357_, 0);
                    v___x_5365_ = (lean_unbox(v_fst_5364_) as u8);
                    if v___x_5365_ == 0 {
                        v_snd_5366_ = lean_ctor_get(v_b_5357_, 1);
                        v_isSharedCheck_5374_ = (!lean_is_exclusive(v_b_5357_)) as u8;
                        if v_isSharedCheck_5374_ == 0 {
                            v_unused_5375_ = lean_ctor_get(v_b_5357_, 0);
                            lean_dec(v_unused_5375_);
                            v___x_5368_ = v_b_5357_;
                            v_isShared_5369_ = v_isSharedCheck_5374_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_5366_);
                            lean_dec(v_b_5357_);
                            v___x_5368_ = lean_box(0);
                            v_isShared_5369_ = v_isSharedCheck_5374_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_5376_ = lean_ctor_get(v_b_5357_, 1);
                        v_isSharedCheck_5386_ = (!lean_is_exclusive(v_b_5357_)) as u8;
                        if v_isSharedCheck_5386_ == 0 {
                            v_unused_5387_ = lean_ctor_get(v_b_5357_, 0);
                            lean_dec(v_unused_5387_);
                            v___x_5378_ = v_b_5357_;
                            v_isShared_5379_ = v_isSharedCheck_5386_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_snd_5376_);
                            lean_dec(v_b_5357_);
                            v___x_5378_ = lean_box(0);
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
                v___x_5370_ = lean_box((v___x_5352_) as usize);
                if v_isShared_5369_ == 0 {
                    lean_ctor_set(v___x_5368_, 0, v___x_5370_);
                    v___x_5372_ = v___x_5368_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5373_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5373_, 0, v___x_5370_);
                    lean_ctor_set(v_reuseFailAlloc_5373_, 1, v_snd_5366_);
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
                lean_inc(v___x_5380_);
                v___x_5381_ = lean_array_push(v_snd_5376_, v___x_5380_);
                v___x_5382_ = lean_box((v___x_5353_) as usize);
                if v_isShared_5379_ == 0 {
                    lean_ctor_set(v___x_5378_, 1, v___x_5381_);
                    lean_ctor_set(v___x_5378_, 0, v___x_5382_);
                    v___x_5384_ = v___x_5378_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5385_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5385_, 0, v___x_5382_);
                    lean_ctor_set(v_reuseFailAlloc_5385_, 1, v___x_5381_);
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
    mut v___x_5388_: *mut LeanObject,
    mut v___x_5389_: *mut LeanObject,
    mut v_as_5390_: *mut LeanObject,
    mut v_i_5391_: *mut LeanObject,
    mut v_stop_5392_: *mut LeanObject,
    mut v_b_5393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2777__boxed_5394_: u8 = 0;
    let mut v___x_2778__boxed_5395_: u8 = 0;
    let mut v_i_boxed_5396_: usize = 0;
    let mut v_stop_boxed_5397_: usize = 0;
    let mut v_res_5398_: *mut LeanObject = core::ptr::null_mut();
    v___x_2777__boxed_5394_ = (lean_unbox(v___x_5388_) as u8);
    v___x_2778__boxed_5395_ = (lean_unbox(v___x_5389_) as u8);
    v_i_boxed_5396_ = lean_unbox_usize(v_i_5391_);
    lean_dec(v_i_5391_);
    v_stop_boxed_5397_ = lean_unbox_usize(v_stop_5392_);
    lean_dec(v_stop_5392_);
    v_res_5398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_2777__boxed_5394_, v___x_2778__boxed_5395_, v_as_5390_, v_i_boxed_5396_, v_stop_boxed_5397_, v_b_5393_);
    lean_dec_ref(v_as_5390_);
    return v_res_5398_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_evalExact(
    mut v_stx_5413_: *mut LeanObject,
    mut v_a_5414_: *mut LeanObject,
    mut v_a_5415_: *mut LeanObject,
    mut v_a_5416_: *mut LeanObject,
    mut v_a_5417_: *mut LeanObject,
    mut v_a_5418_: *mut LeanObject,
    mut v_a_5419_: *mut LeanObject,
    mut v_a_5420_: *mut LeanObject,
    mut v_a_5421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: u8 = 0;
    let mut v___x_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: u8 = 0;
    let mut v_required_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: u8 = 0;
    let mut v___x_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5451_: u8 = 0;
    let mut v_sz_5452_: usize = 0;
    let mut v___x_5453_: usize = 0;
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v_a_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v___y_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5470_: usize = 0;
    let mut v___x_5471_: usize = 0;
    let mut v___x_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: u8 = 0;
    let mut v___x_5478_: u8 = 0;
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: u8 = 0;
    let mut v___x_5486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: u8 = 0;
    let mut v___x_5489_: usize = 0;
    let mut v___x_5490_: usize = 0;
    let mut v___x_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: usize = 0;
    let mut v___x_5494_: usize = 0;
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5423_ = l_Lean_Elab_LibrarySearch_evalExact___closed__1;
                lean_inc(v_stx_5413_);
                v___x_5424_ = l_Lean_Syntax_isOfKind(v_stx_5413_, v___x_5423_);
                if v___x_5424_ == 0 {
                    lean_dec(v_stx_5413_);
                    v___x_5425_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                    return v___x_5425_;
                } else {
                    v___x_5426_ = lean_unsigned_to_nat(1);
                    v___x_5427_ = l_Lean_Syntax_getArg(v_stx_5413_, v___x_5426_);
                    v___x_5428_ = l_Lean_Elab_LibrarySearch_evalExact___closed__3;
                    lean_inc(v___x_5427_);
                    v___x_5429_ = l_Lean_Syntax_isOfKind(v___x_5427_, v___x_5428_);
                    if v___x_5429_ == 0 {
                        lean_dec(v___x_5427_);
                        lean_dec(v_stx_5413_);
                        v___x_5474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                        return v___x_5474_;
                    } else {
                        v___x_5475_ = lean_unsigned_to_nat(2);
                        v___x_5476_ = l_Lean_Syntax_getArg(v_stx_5413_, v___x_5475_);
                        lean_dec(v_stx_5413_);
                        v___x_5477_ = l_Lean_Syntax_isNone(v___x_5476_);
                        if v___x_5477_ == 0 {
                            lean_inc(v___x_5476_);
                            v___x_5478_ = l_Lean_Syntax_matchesNull(v___x_5476_, v___x_5475_);
                            if v___x_5478_ == 0 {
                                lean_dec(v___x_5476_);
                                lean_dec(v___x_5427_);
                                v___x_5479_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                                return v___x_5479_;
                            } else {
                                v___x_5480_ = l_Lean_Syntax_getArg(v___x_5476_, v___x_5426_);
                                lean_dec(v___x_5476_);
                                v___x_5481_ = l_Lean_Syntax_getArgs(v___x_5480_);
                                lean_dec(v___x_5480_);
                                v___x_5482_ = lean_unsigned_to_nat(0);
                                v___x_5483_ = l_Lean_Elab_LibrarySearch_evalExact___closed__4;
                                v___x_5484_ = lean_array_get_size(v___x_5481_);
                                v___x_5485_ = lean_nat_dec_lt(v___x_5482_, v___x_5484_);
                                if v___x_5485_ == 0 {
                                    lean_dec_ref(v___x_5481_);
                                    v___y_5469_ = v___x_5483_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_5486_ = lean_box((v___x_5429_) as usize);
                                    v___x_5487_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_5487_, 0, v___x_5486_);
                                    lean_ctor_set(v___x_5487_, 1, v___x_5483_);
                                    v___x_5488_ = lean_nat_dec_le(v___x_5484_, v___x_5484_);
                                    if v___x_5488_ == 0 {
                                        if v___x_5485_ == 0 {
                                            lean_dec_ref_known(v___x_5487_, 2);
                                            lean_dec_ref(v___x_5481_);
                                            v___y_5469_ = v___x_5483_;
                                            state = 6;
                                            continue;
                                        } else {
                                            v___x_5489_ = 0usize;
                                            v___x_5490_ = lean_usize_of_nat(v___x_5484_);
                                            v___x_5491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5429_, v___x_5477_, v___x_5481_, v___x_5489_, v___x_5490_, v___x_5487_);
                                            lean_dec_ref(v___x_5481_);
                                            v_snd_5492_ = lean_ctor_get(v___x_5491_, 1);
                                            lean_inc(v_snd_5492_);
                                            lean_dec_ref(v___x_5491_);
                                            v___y_5469_ = v_snd_5492_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        v___x_5493_ = 0usize;
                                        v___x_5494_ = lean_usize_of_nat(v___x_5484_);
                                        v___x_5495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5429_, v___x_5477_, v___x_5481_, v___x_5493_, v___x_5494_, v___x_5487_);
                                        lean_dec_ref(v___x_5481_);
                                        v_snd_5496_ = lean_ctor_get(v___x_5495_, 1);
                                        lean_inc(v_snd_5496_);
                                        lean_dec_ref(v___x_5495_);
                                        v___y_5469_ = v_snd_5496_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v___x_5476_);
                            v___x_5497_ = lean_box(0);
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
                v___x_5441_ = lean_alloc_ctor(0, 0, (4) as u32);
                lean_ctor_set_uint8(v___x_5441_, 0 as u32, v___x_5440_);
                lean_ctor_set_uint8(v___x_5441_, 1 as u32, v___x_5440_);
                lean_ctor_set_uint8(v___x_5441_, 2 as u32, v___x_5429_);
                lean_ctor_set_uint8(v___x_5441_, 3 as u32, v___x_5440_);
                v___x_5442_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
                    v___x_5427_,
                    v___x_5441_,
                    v___x_5429_,
                    v___y_5432_,
                    v___y_5438_,
                    v___y_5439_,
                );
                if lean_obj_tag(v___x_5442_) == 0 {
                    if lean_obj_tag(v_required_5431_) == 0 {
                        v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
                        lean_inc(v_a_5443_);
                        lean_dec_ref_known(v___x_5442_, 1);
                        v_ref_5444_ = lean_ctor_get(v___y_5438_, 5);
                        lean_inc(v_ref_5444_);
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
                        v_a_5446_ = lean_ctor_get(v___x_5442_, 0);
                        lean_inc(v_a_5446_);
                        lean_dec_ref_known(v___x_5442_, 1);
                        v_ref_5447_ = lean_ctor_get(v___y_5438_, 5);
                        v_val_5448_ = lean_ctor_get(v_required_5431_, 0);
                        v_isSharedCheck_5459_ = (!lean_is_exclusive(v_required_5431_)) as u8;
                        if v_isSharedCheck_5459_ == 0 {
                            v___x_5450_ = v_required_5431_;
                            v_isShared_5451_ = v_isSharedCheck_5459_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_5448_);
                            lean_dec(v_required_5431_);
                            v___x_5450_ = lean_box(0);
                            v_isShared_5451_ = v_isSharedCheck_5459_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_required_5431_);
                    v_a_5460_ = lean_ctor_get(v___x_5442_, 0);
                    v_isSharedCheck_5467_ = (!lean_is_exclusive(v___x_5442_)) as u8;
                    if v_isSharedCheck_5467_ == 0 {
                        v___x_5462_ = v___x_5442_;
                        v_isShared_5463_ = v_isSharedCheck_5467_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5460_);
                        lean_dec(v___x_5442_);
                        v___x_5462_ = lean_box(0);
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
                    lean_ctor_set(v___x_5450_, 0, v___x_5454_);
                    v___x_5456_ = v___x_5450_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5458_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5454_);
                    v___x_5456_ = v_reuseFailAlloc_5458_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_ref_5447_);
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
                    v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
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
                if lean_obj_tag(v___x_5472_) == 0 {
                    lean_dec(v___x_5427_);
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
    mut v_stx_5498_: *mut LeanObject,
    mut v_a_5499_: *mut LeanObject,
    mut v_a_5500_: *mut LeanObject,
    mut v_a_5501_: *mut LeanObject,
    mut v_a_5502_: *mut LeanObject,
    mut v_a_5503_: *mut LeanObject,
    mut v_a_5504_: *mut LeanObject,
    mut v_a_5505_: *mut LeanObject,
    mut v_a_5506_: *mut LeanObject,
    mut v_a_5507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5508_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5506_);
    lean_dec_ref(v_a_5505_);
    lean_dec(v_a_5504_);
    lean_dec_ref(v_a_5503_);
    lean_dec(v_a_5502_);
    lean_dec_ref(v_a_5501_);
    lean_dec(v_a_5500_);
    lean_dec_ref(v_a_5499_);
    return v_res_5508_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1()
-> *mut LeanObject {
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    v___x_5517_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5518_ = l_Lean_Elab_LibrarySearch_evalExact___closed__1;
    v___x_5519_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2;
    v___x_5520_ = lean_alloc_closure(
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
    mut v_a_5522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5523_: *mut LeanObject = core::ptr::null_mut();
    v_res_5523_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1();
    return v_res_5523_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3()
-> *mut LeanObject {
    let mut v___x_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
    v___x_5550_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1___closed__2;
    v___x_5551_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___closed__6;
    v___x_5552_ = l_Lean_addBuiltinDeclarationRanges(v___x_5550_, v___x_5551_);
    return v___x_5552_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3___boxed(
    mut v_a_5553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5554_: *mut LeanObject = core::ptr::null_mut();
    v_res_5554_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3();
    return v_res_5554_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalApply_spec__0(
    mut v_sz_5555_: usize,
    mut v_i_5556_: usize,
    mut v_bs_5557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: usize = 0;
    let mut v___x_5564_: usize = 0;
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5558_ = lean_usize_dec_lt(v_i_5556_, v_sz_5555_);
                if v___x_5558_ == 0 {
                    v___x_5559_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5559_, 0, v_bs_5557_);
                    return v___x_5559_;
                } else {
                    v_v_5560_ = lean_array_uget(v_bs_5557_, v_i_5556_);
                    v___x_5561_ = lean_unsigned_to_nat(0);
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
    mut v_sz_5567_: *mut LeanObject,
    mut v_i_5568_: *mut LeanObject,
    mut v_bs_5569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5570_: usize = 0;
    let mut v_i_boxed_5571_: usize = 0;
    let mut v_res_5572_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5570_ = lean_unbox_usize(v_sz_5567_);
    lean_dec(v_sz_5567_);
    v_i_boxed_5571_ = lean_unbox_usize(v_i_5568_);
    lean_dec(v_i_5568_);
    v_res_5572_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_LibrarySearch_evalApply_spec__0(v_sz_boxed_5570_, v_i_boxed_5571_, v_bs_5569_);
    return v_res_5572_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_evalApply(
    mut v_stx_5578_: *mut LeanObject,
    mut v_a_5579_: *mut LeanObject,
    mut v_a_5580_: *mut LeanObject,
    mut v_a_5581_: *mut LeanObject,
    mut v_a_5582_: *mut LeanObject,
    mut v_a_5583_: *mut LeanObject,
    mut v_a_5584_: *mut LeanObject,
    mut v_a_5585_: *mut LeanObject,
    mut v_a_5586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: u8 = 0;
    let mut v___x_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v_required_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: u8 = 0;
    let mut v___x_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5614_: u8 = 0;
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5618_: u8 = 0;
    let mut v___y_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5621_: usize = 0;
    let mut v___x_5622_: usize = 0;
    let mut v___x_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: u8 = 0;
    let mut v___x_5629_: u8 = 0;
    let mut v___x_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: u8 = 0;
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: u8 = 0;
    let mut v___x_5640_: usize = 0;
    let mut v___x_5641_: usize = 0;
    let mut v___x_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: usize = 0;
    let mut v___x_5645_: usize = 0;
    let mut v___x_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5588_ = l_Lean_Elab_LibrarySearch_evalApply___closed__0;
                lean_inc(v_stx_5578_);
                v___x_5589_ = l_Lean_Syntax_isOfKind(v_stx_5578_, v___x_5588_);
                if v___x_5589_ == 0 {
                    lean_dec(v_stx_5578_);
                    v___x_5590_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                    return v___x_5590_;
                } else {
                    v___x_5591_ = lean_unsigned_to_nat(1);
                    v___x_5592_ = l_Lean_Syntax_getArg(v_stx_5578_, v___x_5591_);
                    v___x_5593_ = l_Lean_Elab_LibrarySearch_evalExact___closed__3;
                    lean_inc(v___x_5592_);
                    v___x_5594_ = l_Lean_Syntax_isOfKind(v___x_5592_, v___x_5593_);
                    if v___x_5594_ == 0 {
                        lean_dec(v___x_5592_);
                        lean_dec(v_stx_5578_);
                        v___x_5625_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                        return v___x_5625_;
                    } else {
                        v___x_5626_ = lean_unsigned_to_nat(2);
                        v___x_5627_ = l_Lean_Syntax_getArg(v_stx_5578_, v___x_5626_);
                        lean_dec(v_stx_5578_);
                        v___x_5628_ = l_Lean_Syntax_isNone(v___x_5627_);
                        if v___x_5628_ == 0 {
                            lean_inc(v___x_5627_);
                            v___x_5629_ = l_Lean_Syntax_matchesNull(v___x_5627_, v___x_5626_);
                            if v___x_5629_ == 0 {
                                lean_dec(v___x_5627_);
                                lean_dec(v___x_5592_);
                                v___x_5630_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg();
                                return v___x_5630_;
                            } else {
                                v___x_5631_ = l_Lean_Syntax_getArg(v___x_5627_, v___x_5591_);
                                lean_dec(v___x_5627_);
                                v___x_5632_ = l_Lean_Syntax_getArgs(v___x_5631_);
                                lean_dec(v___x_5631_);
                                v___x_5633_ = lean_unsigned_to_nat(0);
                                v___x_5634_ = l_Lean_Elab_LibrarySearch_evalExact___closed__4;
                                v___x_5635_ = lean_array_get_size(v___x_5632_);
                                v___x_5636_ = lean_nat_dec_lt(v___x_5633_, v___x_5635_);
                                if v___x_5636_ == 0 {
                                    lean_dec_ref(v___x_5632_);
                                    v___y_5620_ = v___x_5634_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_5637_ = lean_box((v___x_5594_) as usize);
                                    v___x_5638_ = lean_alloc_ctor(0, 2, (0) as u32);
                                    lean_ctor_set(v___x_5638_, 0, v___x_5637_);
                                    lean_ctor_set(v___x_5638_, 1, v___x_5634_);
                                    v___x_5639_ = lean_nat_dec_le(v___x_5635_, v___x_5635_);
                                    if v___x_5639_ == 0 {
                                        if v___x_5636_ == 0 {
                                            lean_dec_ref_known(v___x_5638_, 2);
                                            lean_dec_ref(v___x_5632_);
                                            v___y_5620_ = v___x_5634_;
                                            state = 4;
                                            continue;
                                        } else {
                                            v___x_5640_ = 0usize;
                                            v___x_5641_ = lean_usize_of_nat(v___x_5635_);
                                            v___x_5642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5594_, v___x_5628_, v___x_5632_, v___x_5640_, v___x_5641_, v___x_5638_);
                                            lean_dec_ref(v___x_5632_);
                                            v_snd_5643_ = lean_ctor_get(v___x_5642_, 1);
                                            lean_inc(v_snd_5643_);
                                            lean_dec_ref(v___x_5642_);
                                            v___y_5620_ = v_snd_5643_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        v___x_5644_ = 0usize;
                                        v___x_5645_ = lean_usize_of_nat(v___x_5635_);
                                        v___x_5646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_LibrarySearch_evalExact_spec__3(v___x_5594_, v___x_5628_, v___x_5632_, v___x_5644_, v___x_5645_, v___x_5638_);
                                        lean_dec_ref(v___x_5632_);
                                        v_snd_5647_ = lean_ctor_get(v___x_5646_, 1);
                                        lean_inc(v_snd_5647_);
                                        lean_dec_ref(v___x_5646_);
                                        v___y_5620_ = v_snd_5647_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v___x_5627_);
                            v___x_5648_ = lean_box(0);
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
                v___x_5606_ = lean_alloc_ctor(0, 0, (4) as u32);
                lean_ctor_set_uint8(v___x_5606_, 0 as u32, v___x_5605_);
                lean_ctor_set_uint8(v___x_5606_, 1 as u32, v___x_5605_);
                lean_ctor_set_uint8(v___x_5606_, 2 as u32, v___x_5594_);
                lean_ctor_set_uint8(v___x_5606_, 3 as u32, v___x_5605_);
                v___x_5607_ = l_Lean_Elab_LibrarySearch_elabLibrarySearchConfig___redArg(
                    v___x_5592_,
                    v___x_5606_,
                    v___x_5594_,
                    v___y_5597_,
                    v___y_5603_,
                    v___y_5604_,
                );
                if lean_obj_tag(v___x_5607_) == 0 {
                    v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
                    lean_inc(v_a_5608_);
                    lean_dec_ref_known(v___x_5607_, 1);
                    v_ref_5609_ = lean_ctor_get(v___y_5603_, 5);
                    lean_inc(v_ref_5609_);
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
                    lean_dec(v_required_5596_);
                    v_a_5611_ = lean_ctor_get(v___x_5607_, 0);
                    v_isSharedCheck_5618_ = (!lean_is_exclusive(v___x_5607_)) as u8;
                    if v_isSharedCheck_5618_ == 0 {
                        v___x_5613_ = v___x_5607_;
                        v_isShared_5614_ = v_isSharedCheck_5618_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5611_);
                        lean_dec(v___x_5607_);
                        v___x_5613_ = lean_box(0);
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
                    v_reuseFailAlloc_5617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5617_, 0, v_a_5611_);
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
                if lean_obj_tag(v___x_5623_) == 0 {
                    lean_dec(v___x_5592_);
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
    mut v_stx_5649_: *mut LeanObject,
    mut v_a_5650_: *mut LeanObject,
    mut v_a_5651_: *mut LeanObject,
    mut v_a_5652_: *mut LeanObject,
    mut v_a_5653_: *mut LeanObject,
    mut v_a_5654_: *mut LeanObject,
    mut v_a_5655_: *mut LeanObject,
    mut v_a_5656_: *mut LeanObject,
    mut v_a_5657_: *mut LeanObject,
    mut v_a_5658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5659_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_5657_);
    lean_dec_ref(v_a_5656_);
    lean_dec(v_a_5655_);
    lean_dec_ref(v_a_5654_);
    lean_dec(v_a_5653_);
    lean_dec_ref(v_a_5652_);
    lean_dec(v_a_5651_);
    lean_dec_ref(v_a_5650_);
    return v_res_5659_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1()
-> *mut LeanObject {
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5671_: *mut LeanObject = core::ptr::null_mut();
    v___x_5667_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_5668_ = l_Lean_Elab_LibrarySearch_evalApply___closed__0;
    v___x_5669_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1;
    v___x_5670_ = lean_alloc_closure(
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
    mut v_a_5672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5673_: *mut LeanObject = core::ptr::null_mut();
    v_res_5673_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1();
    return v_res_5673_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3()
-> *mut LeanObject {
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    v___x_5700_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1___closed__1;
    v___x_5701_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___closed__6;
    v___x_5702_ = l_Lean_addBuiltinDeclarationRanges(v___x_5700_, v___x_5701_);
    return v___x_5702_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3___boxed(
    mut v_a_5703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5704_: *mut LeanObject = core::ptr::null_mut();
    v_res_5704_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3();
    return v_res_5704_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    v___x_5706_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_evalExact_spec__0___redArg___closed__0);
    v___x_5707_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_5707_, 0, v___x_5706_);
    return v___x_5707_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg___boxed(
    mut v___y_5708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5709_: *mut LeanObject = core::ptr::null_mut();
    v_res_5709_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg();
    return v_res_5709_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0(
    mut v_00_u03b1_5710_: *mut LeanObject,
    mut v___y_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
    mut v___y_5714_: *mut LeanObject,
    mut v___y_5715_: *mut LeanObject,
    mut v___y_5716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    v___x_5718_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg();
    return v___x_5718_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___boxed(
    mut v_00_u03b1_5719_: *mut LeanObject,
    mut v___y_5720_: *mut LeanObject,
    mut v___y_5721_: *mut LeanObject,
    mut v___y_5722_: *mut LeanObject,
    mut v___y_5723_: *mut LeanObject,
    mut v___y_5724_: *mut LeanObject,
    mut v___y_5725_: *mut LeanObject,
    mut v___y_5726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5727_: *mut LeanObject = core::ptr::null_mut();
    v_res_5727_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0(v_00_u03b1_5719_, v___y_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
    lean_dec(v___y_5725_);
    lean_dec_ref(v___y_5724_);
    lean_dec(v___y_5723_);
    lean_dec_ref(v___y_5722_);
    lean_dec(v___y_5721_);
    lean_dec_ref(v___y_5720_);
    return v_res_5727_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0(
    mut v_x_5728_: *mut LeanObject,
    mut v___y_5729_: *mut LeanObject,
    mut v___y_5730_: *mut LeanObject,
    mut v___y_5731_: *mut LeanObject,
    mut v___y_5732_: *mut LeanObject,
    mut v___y_5733_: *mut LeanObject,
    mut v___y_5734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_5730_);
    lean_inc_ref(v___y_5729_);
    v___x_5736_ = lean_apply_7(
        v_x_5728_,
        v___y_5729_,
        v___y_5730_,
        v___y_5731_,
        v___y_5732_,
        v___y_5733_,
        v___y_5734_,
        lean_box(0),
    );
    return v___x_5736_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0___boxed(
    mut v_x_5737_: *mut LeanObject,
    mut v___y_5738_: *mut LeanObject,
    mut v___y_5739_: *mut LeanObject,
    mut v___y_5740_: *mut LeanObject,
    mut v___y_5741_: *mut LeanObject,
    mut v___y_5742_: *mut LeanObject,
    mut v___y_5743_: *mut LeanObject,
    mut v___y_5744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5745_: *mut LeanObject = core::ptr::null_mut();
    v_res_5745_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0(v_x_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
    lean_dec(v___y_5739_);
    lean_dec_ref(v___y_5738_);
    return v_res_5745_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(
    mut v_mvarId_5746_: *mut LeanObject,
    mut v_x_5747_: *mut LeanObject,
    mut v___y_5748_: *mut LeanObject,
    mut v___y_5749_: *mut LeanObject,
    mut v___y_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5760_: u8 = 0;
    let mut v___x_5762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_5749_);
                lean_inc_ref(v___y_5748_);
                v___f_5755_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                lean_closure_set(v___f_5755_, 0, v_x_5747_);
                lean_closure_set(v___f_5755_, 1, v___y_5748_);
                lean_closure_set(v___f_5755_, 2, v___y_5749_);
                v___x_5756_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_5746_,
                    v___f_5755_,
                    v___y_5750_,
                    v___y_5751_,
                    v___y_5752_,
                    v___y_5753_,
                );
                if lean_obj_tag(v___x_5756_) == 0 {
                    return v___x_5756_;
                } else {
                    v_a_5757_ = lean_ctor_get(v___x_5756_, 0);
                    v_isSharedCheck_5764_ = (!lean_is_exclusive(v___x_5756_)) as u8;
                    if v_isSharedCheck_5764_ == 0 {
                        v___x_5759_ = v___x_5756_;
                        v_isShared_5760_ = v_isSharedCheck_5764_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5757_);
                        lean_dec(v___x_5756_);
                        v___x_5759_ = lean_box(0);
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
                    v_reuseFailAlloc_5763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5763_, 0, v_a_5757_);
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
    mut v_mvarId_5765_: *mut LeanObject,
    mut v_x_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
    mut v___y_5768_: *mut LeanObject,
    mut v___y_5769_: *mut LeanObject,
    mut v___y_5770_: *mut LeanObject,
    mut v___y_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5774_: *mut LeanObject = core::ptr::null_mut();
    v_res_5774_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(v_mvarId_5765_, v_x_5766_, v___y_5767_, v___y_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
    lean_dec(v___y_5772_);
    lean_dec_ref(v___y_5771_);
    lean_dec(v___y_5770_);
    lean_dec_ref(v___y_5769_);
    lean_dec(v___y_5768_);
    lean_dec_ref(v___y_5767_);
    return v_res_5774_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2(
    mut v_00_u03b1_5775_: *mut LeanObject,
    mut v_mvarId_5776_: *mut LeanObject,
    mut v_x_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
    mut v___y_5779_: *mut LeanObject,
    mut v___y_5780_: *mut LeanObject,
    mut v___y_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    v___x_5785_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(v_mvarId_5776_, v_x_5777_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
    return v___x_5785_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___boxed(
    mut v_00_u03b1_5786_: *mut LeanObject,
    mut v_mvarId_5787_: *mut LeanObject,
    mut v_x_5788_: *mut LeanObject,
    mut v___y_5789_: *mut LeanObject,
    mut v___y_5790_: *mut LeanObject,
    mut v___y_5791_: *mut LeanObject,
    mut v___y_5792_: *mut LeanObject,
    mut v___y_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5796_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5794_);
    lean_dec_ref(v___y_5793_);
    lean_dec(v___y_5792_);
    lean_dec_ref(v___y_5791_);
    lean_dec(v___y_5790_);
    lean_dec_ref(v___y_5789_);
    return v_res_5796_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__0(
    mut v_g_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
    mut v___y_5801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: u8 = 0;
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    v___x_5803_ = lean_box(0);
    v___x_5804_ = 0;
    v___x_5805_ = lean_unsigned_to_nat(6);
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
    mut v_g_5807_: *mut LeanObject,
    mut v___y_5808_: *mut LeanObject,
    mut v___y_5809_: *mut LeanObject,
    mut v___y_5810_: *mut LeanObject,
    mut v___y_5811_: *mut LeanObject,
    mut v___y_5812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5813_: *mut LeanObject = core::ptr::null_mut();
    v_res_5813_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__0(
        v_g_5807_,
        v___y_5808_,
        v___y_5809_,
        v___y_5810_,
        v___y_5811_,
    );
    lean_dec(v___y_5811_);
    lean_dec_ref(v___y_5810_);
    lean_dec(v___y_5809_);
    lean_dec_ref(v___y_5808_);
    return v_res_5813_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1(
    mut v___x_5814_: u8,
    mut v_x_5815_: *mut LeanObject,
    mut v___y_5816_: *mut LeanObject,
    mut v___y_5817_: *mut LeanObject,
    mut v___y_5818_: *mut LeanObject,
    mut v___y_5819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    v___x_5821_ = lean_box((v___x_5814_) as usize);
    v___x_5822_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5822_, 0, v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1___boxed(
    mut v___x_5823_: *mut LeanObject,
    mut v_x_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
    mut v___y_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6766__boxed_5830_: u8 = 0;
    let mut v_res_5831_: *mut LeanObject = core::ptr::null_mut();
    v___x_6766__boxed_5830_ = (lean_unbox(v___x_5823_) as u8);
    v_res_5831_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1(
        v___x_6766__boxed_5830_,
        v_x_5824_,
        v___y_5825_,
        v___y_5826_,
        v___y_5827_,
        v___y_5828_,
    );
    lean_dec(v___y_5828_);
    lean_dec_ref(v___y_5827_);
    lean_dec(v___y_5826_);
    lean_dec_ref(v___y_5825_);
    lean_dec(v_x_5824_);
    return v_res_5831_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(
    mut v_ref_5832_: *mut LeanObject,
    mut v_msgData_5833_: *mut LeanObject,
    mut v_severity_5834_: u8,
    mut v_isSilent_5835_: u8,
    mut v___y_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v___y_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5845_: u8 = 0;
    let mut v___y_5846_: u8 = 0;
    let mut v___y_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5865_: u8 = 0;
    let mut v___x_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5876_: u8 = 0;
    let mut v___y_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5881_: u8 = 0;
    let mut v___y_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5883_: u8 = 0;
    let mut v___y_5884_: u8 = 0;
    let mut v___y_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5891_: u8 = 0;
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: u8 = 0;
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5901_: u8 = 0;
    let mut v___y_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5907_: u8 = 0;
    let mut v___y_5908_: u8 = 0;
    let mut v___y_5909_: u8 = 0;
    let mut v___y_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5917_: u8 = 0;
    let mut v___y_5918_: u8 = 0;
    let mut v___y_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5920_: u8 = 0;
    let mut v_ref_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: u8 = 0;
    let mut v___y_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: u8 = 0;
    let mut v___y_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: u8 = 0;
    let mut v___y_5933_: u8 = 0;
    let mut v___y_5935_: u8 = 0;
    let mut v_fileName_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5940_: u8 = 0;
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: u8 = 0;
    let mut v___x_5945_: u8 = 0;
    let mut v___x_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: u8 = 0;
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_5833_);
                    v___x_5951_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5833_);
                    v___y_5935_ = v___x_5951_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5851_ = lean_st_ref_take(v___y_5850_);
                v_currNamespace_5852_ = lean_ctor_get(v___y_5849_, 6);
                v_openDecls_5853_ = lean_ctor_get(v___y_5849_, 7);
                v_env_5854_ = lean_ctor_get(v___x_5851_, 0);
                v_nextMacroScope_5855_ = lean_ctor_get(v___x_5851_, 1);
                v_ngen_5856_ = lean_ctor_get(v___x_5851_, 2);
                v_auxDeclNGen_5857_ = lean_ctor_get(v___x_5851_, 3);
                v_traceState_5858_ = lean_ctor_get(v___x_5851_, 4);
                v_cache_5859_ = lean_ctor_get(v___x_5851_, 5);
                v_messages_5860_ = lean_ctor_get(v___x_5851_, 6);
                v_infoState_5861_ = lean_ctor_get(v___x_5851_, 7);
                v_snapshotTasks_5862_ = lean_ctor_get(v___x_5851_, 8);
                v_isSharedCheck_5876_ = (!lean_is_exclusive(v___x_5851_)) as u8;
                if v_isSharedCheck_5876_ == 0 {
                    v___x_5864_ = v___x_5851_;
                    v_isShared_5865_ = v_isSharedCheck_5876_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5862_);
                    lean_inc(v_infoState_5861_);
                    lean_inc(v_messages_5860_);
                    lean_inc(v_cache_5859_);
                    lean_inc(v_traceState_5858_);
                    lean_inc(v_auxDeclNGen_5857_);
                    lean_inc(v_ngen_5856_);
                    lean_inc(v_nextMacroScope_5855_);
                    lean_inc(v_env_5854_);
                    lean_dec(v___x_5851_);
                    v___x_5864_ = lean_box(0);
                    v_isShared_5865_ = v_isSharedCheck_5876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_5853_);
                lean_inc(v_currNamespace_5852_);
                v___x_5866_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5866_, 0, v_currNamespace_5852_);
                lean_ctor_set(v___x_5866_, 1, v_openDecls_5853_);
                v___x_5867_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5867_, 0, v___x_5866_);
                lean_ctor_set(v___x_5867_, 1, v___y_5844_);
                lean_inc_ref(v___y_5847_);
                lean_inc_ref(v___y_5843_);
                v___x_5868_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_5868_, 0, v___y_5843_);
                lean_ctor_set(v___x_5868_, 1, v___y_5848_);
                lean_ctor_set(v___x_5868_, 2, v___y_5842_);
                lean_ctor_set(v___x_5868_, 3, v___y_5847_);
                lean_ctor_set(v___x_5868_, 4, v___x_5867_);
                lean_ctor_set_uint8(
                    v___x_5868_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_5846_,
                );
                lean_ctor_set_uint8(
                    v___x_5868_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_5845_,
                );
                lean_ctor_set_uint8(
                    v___x_5868_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5835_,
                );
                v___x_5869_ = l_Lean_MessageLog_add(v___x_5868_, v_messages_5860_);
                if v_isShared_5865_ == 0 {
                    lean_ctor_set(v___x_5864_, 6, v___x_5869_);
                    v___x_5871_ = v___x_5864_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5875_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_env_5854_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 1, v_nextMacroScope_5855_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 2, v_ngen_5856_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 3, v_auxDeclNGen_5857_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 4, v_traceState_5858_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 5, v_cache_5859_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 6, v___x_5869_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 7, v_infoState_5861_);
                    lean_ctor_set(v_reuseFailAlloc_5875_, 8, v_snapshotTasks_5862_);
                    v___x_5871_ = v_reuseFailAlloc_5875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5872_ = lean_st_ref_set(v___y_5850_, v___x_5871_);
                v___x_5873_ = lean_box(0);
                v___x_5874_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5874_, 0, v___x_5873_);
                return v___x_5874_;
            }
            4 => {
                v___x_5886_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5833_,
                    );
                v___x_5887_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig_evalExpr_spec__1_spec__1(v___x_5886_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
                v_a_5888_ = lean_ctor_get(v___x_5887_, 0);
                v_isSharedCheck_5901_ = (!lean_is_exclusive(v___x_5887_)) as u8;
                if v_isSharedCheck_5901_ == 0 {
                    v___x_5890_ = v___x_5887_;
                    v_isShared_5891_ = v_isSharedCheck_5901_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_5888_);
                    lean_dec(v___x_5887_);
                    v___x_5890_ = lean_box(0);
                    v_isShared_5891_ = v_isSharedCheck_5901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_5880_, 2);
                v___x_5892_ = l_Lean_FileMap_toPosition(v___y_5880_, v___y_5882_);
                lean_dec(v___y_5882_);
                v___x_5893_ = l_Lean_FileMap_toPosition(v___y_5880_, v___y_5885_);
                lean_dec(v___y_5885_);
                v___x_5894_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5894_, 0, v___x_5893_);
                v___x_5895_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___closed__0;
                if v___y_5881_ == 0 {
                    lean_del_object(v___x_5890_);
                    lean_dec_ref(v___y_5878_);
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
                    lean_inc(v_a_5888_);
                    v___x_5896_ = l_Lean_MessageData_hasTag(v___y_5878_, v_a_5888_);
                    if v___x_5896_ == 0 {
                        lean_dec_ref_known(v___x_5894_, 1);
                        lean_dec_ref(v___x_5892_);
                        lean_dec(v_a_5888_);
                        v___x_5897_ = lean_box(0);
                        if v_isShared_5891_ == 0 {
                            lean_ctor_set(v___x_5890_, 0, v___x_5897_);
                            v___x_5899_ = v___x_5890_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5897_);
                            v___x_5899_ = v_reuseFailAlloc_5900_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5890_);
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
                lean_dec(v___y_5905_);
                if lean_obj_tag(v___x_5911_) == 0 {
                    lean_inc(v___y_5910_);
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
                    v_val_5912_ = lean_ctor_get(v___x_5911_, 0);
                    lean_inc(v_val_5912_);
                    lean_dec_ref_known(v___x_5911_, 1);
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
                if lean_obj_tag(v___x_5922_) == 0 {
                    v___x_5923_ = lean_unsigned_to_nat(0);
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
                    v_val_5924_ = lean_ctor_get(v___x_5922_, 0);
                    lean_inc(v_val_5924_);
                    lean_dec_ref_known(v___x_5922_, 1);
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
                    v_fileName_5936_ = lean_ctor_get(v___y_5838_, 0);
                    v_fileMap_5937_ = lean_ctor_get(v___y_5838_, 1);
                    v_options_5938_ = lean_ctor_get(v___y_5838_, 2);
                    v_ref_5939_ = lean_ctor_get(v___y_5838_, 5);
                    v_suppressElabErrors_5940_ = lean_ctor_get_uint8(
                        v___y_5838_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5941_ = lean_box((v___y_5935_) as usize);
                    v___x_5942_ = lean_box((v_suppressElabErrors_5940_) as usize);
                    v___f_5943_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_exact_x3f_spec__9_spec__9_spec__11___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_5943_, 0, v___x_5941_);
                    lean_closure_set(v___f_5943_, 1, v___x_5942_);
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
                    lean_dec_ref(v_msgData_5833_);
                    v___x_5948_ = lean_box(0);
                    v___x_5949_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5949_, 0, v___x_5948_);
                    return v___x_5949_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_ref_5952_: *mut LeanObject,
    mut v_msgData_5953_: *mut LeanObject,
    mut v_severity_5954_: *mut LeanObject,
    mut v_isSilent_5955_: *mut LeanObject,
    mut v___y_5956_: *mut LeanObject,
    mut v___y_5957_: *mut LeanObject,
    mut v___y_5958_: *mut LeanObject,
    mut v___y_5959_: *mut LeanObject,
    mut v___y_5960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5961_: u8 = 0;
    let mut v_isSilent_boxed_5962_: u8 = 0;
    let mut v_res_5963_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5961_ = (lean_unbox(v_severity_5954_) as u8);
    v_isSilent_boxed_5962_ = (lean_unbox(v_isSilent_5955_) as u8);
    v_res_5963_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(v_ref_5952_, v_msgData_5953_, v_severity_boxed_5961_, v_isSilent_boxed_5962_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_);
    lean_dec(v___y_5959_);
    lean_dec_ref(v___y_5958_);
    lean_dec(v___y_5957_);
    lean_dec_ref(v___y_5956_);
    lean_dec(v_ref_5952_);
    return v_res_5963_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1(
    mut v_msgData_5964_: *mut LeanObject,
    mut v_severity_5965_: u8,
    mut v_isSilent_5966_: u8,
    mut v___y_5967_: *mut LeanObject,
    mut v___y_5968_: *mut LeanObject,
    mut v___y_5969_: *mut LeanObject,
    mut v___y_5970_: *mut LeanObject,
    mut v___y_5971_: *mut LeanObject,
    mut v___y_5972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    v_ref_5974_ = lean_ctor_get(v___y_5971_, 5);
    v___x_5975_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(v_ref_5974_, v_msgData_5964_, v_severity_5965_, v_isSilent_5966_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
    return v___x_5975_;
}
pub unsafe fn l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1___boxed(
    mut v_msgData_5976_: *mut LeanObject,
    mut v_severity_5977_: *mut LeanObject,
    mut v_isSilent_5978_: *mut LeanObject,
    mut v___y_5979_: *mut LeanObject,
    mut v___y_5980_: *mut LeanObject,
    mut v___y_5981_: *mut LeanObject,
    mut v___y_5982_: *mut LeanObject,
    mut v___y_5983_: *mut LeanObject,
    mut v___y_5984_: *mut LeanObject,
    mut v___y_5985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5986_: u8 = 0;
    let mut v_isSilent_boxed_5987_: u8 = 0;
    let mut v_res_5988_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5986_ = (lean_unbox(v_severity_5977_) as u8);
    v_isSilent_boxed_5987_ = (lean_unbox(v_isSilent_5978_) as u8);
    v_res_5988_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1(v_msgData_5976_, v_severity_boxed_5986_, v_isSilent_boxed_5987_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_);
    lean_dec(v___y_5984_);
    lean_dec_ref(v___y_5983_);
    lean_dec(v___y_5982_);
    lean_dec_ref(v___y_5981_);
    lean_dec(v___y_5980_);
    lean_dec_ref(v___y_5979_);
    return v_res_5988_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(
    mut v_msgData_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
    mut v___y_5994_: *mut LeanObject,
    mut v___y_5995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5997_: u8 = 0;
    let mut v___x_5998_: u8 = 0;
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    v___x_5997_ = 2;
    v___x_5998_ = 0;
    v___x_5999_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1(v_msgData_5989_, v___x_5997_, v___x_5998_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
    return v___x_5999_;
}
pub unsafe fn l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1___boxed(
    mut v_msgData_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
    mut v___y_6003_: *mut LeanObject,
    mut v___y_6004_: *mut LeanObject,
    mut v___y_6005_: *mut LeanObject,
    mut v___y_6006_: *mut LeanObject,
    mut v___y_6007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6008_: *mut LeanObject = core::ptr::null_mut();
    v_res_6008_ = l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(
        v_msgData_6000_,
        v___y_6001_,
        v___y_6002_,
        v___y_6003_,
        v___y_6004_,
        v___y_6005_,
        v___y_6006_,
    );
    lean_dec(v___y_6006_);
    lean_dec_ref(v___y_6005_);
    lean_dec(v___y_6004_);
    lean_dec_ref(v___y_6003_);
    lean_dec(v___y_6002_);
    lean_dec_ref(v___y_6001_);
    return v_res_6008_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2()
-> *mut LeanObject {
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut LeanObject = core::ptr::null_mut();
    v___x_6012_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__1;
    v___x_6013_ = l_Lean_MessageData_ofFormat(v___x_6012_);
    return v___x_6013_;
}
pub unsafe fn _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5()
-> *mut LeanObject {
    let mut v___x_6017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    v___x_6017_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__4;
    v___x_6018_ = l_Lean_MessageData_ofFormat(v___x_6017_);
    return v___x_6018_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2(
    mut v_snd_6020_: *mut LeanObject,
    mut v___f_6021_: *mut LeanObject,
    mut v___f_6022_: *mut LeanObject,
    mut v___x_6023_: *mut LeanObject,
    mut v___x_6024_: u8,
    mut v___x_6025_: u8,
    mut v_expectedType_6026_: *mut LeanObject,
    mut v_a_6027_: *mut LeanObject,
    mut v_stx_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: u8 = 0;
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6048_: u8 = 0;
    let mut v___x_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v___x_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6074_: u8 = 0;
    let mut v___x_6076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6078_: u8 = 0;
    let mut v_a_6079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___x_6084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_6036_) == 0 {
                    v_a_6037_ = lean_ctor_get(v___x_6036_, 0);
                    lean_inc(v_a_6037_);
                    lean_dec_ref_known(v___x_6036_, 1);
                    if lean_obj_tag(v_a_6037_) == 1 {
                        lean_dec(v_stx_6028_);
                        lean_dec_ref(v_a_6027_);
                        v_val_6038_ = lean_ctor_get(v_a_6037_, 0);
                        lean_inc(v_val_6038_);
                        lean_dec_ref_known(v_a_6037_, 1);
                        v___x_6039_ = lean_array_get_size(v_val_6038_);
                        lean_dec(v_val_6038_);
                        v___x_6040_ = lean_unsigned_to_nat(0);
                        v___x_6041_ = lean_nat_dec_eq(v___x_6039_, v___x_6040_);
                        if v___x_6041_ == 0 {
                            v___x_6042_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2_once), _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__2);
                            v___x_6043_ = l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(v___x_6042_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
                            if lean_obj_tag(v___x_6043_) == 0 {
                                lean_dec_ref_known(v___x_6043_, 1);
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
                                lean_dec_ref(v_expectedType_6026_);
                                v_a_6045_ = lean_ctor_get(v___x_6043_, 0);
                                v_isSharedCheck_6052_ = (!lean_is_exclusive(v___x_6043_)) as u8;
                                if v_isSharedCheck_6052_ == 0 {
                                    v___x_6047_ = v___x_6043_;
                                    v_isShared_6048_ = v_isSharedCheck_6052_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_6045_);
                                    lean_dec(v___x_6043_);
                                    v___x_6047_ = lean_box(0);
                                    v_isShared_6048_ = v_isSharedCheck_6052_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_6053_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5_once), _init_l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___closed__5);
                            v___x_6054_ = l_Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1(v___x_6053_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
                            if lean_obj_tag(v___x_6054_) == 0 {
                                lean_dec_ref_known(v___x_6054_, 1);
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
                                lean_dec_ref(v_expectedType_6026_);
                                v_a_6056_ = lean_ctor_get(v___x_6054_, 0);
                                v_isSharedCheck_6063_ = (!lean_is_exclusive(v___x_6054_)) as u8;
                                if v_isSharedCheck_6063_ == 0 {
                                    v___x_6058_ = v___x_6054_;
                                    v_isShared_6059_ = v_isSharedCheck_6063_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_6056_);
                                    lean_dec(v___x_6054_);
                                    v___x_6058_ = lean_box(0);
                                    v_isShared_6059_ = v_isSharedCheck_6063_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_6037_);
                        lean_dec_ref(v_expectedType_6026_);
                        lean_inc_ref(v_a_6027_);
                        v___x_6064_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_6027_, v___y_6032_);
                        v_a_6065_ = lean_ctor_get(v___x_6064_, 0);
                        lean_inc(v_a_6065_);
                        lean_dec_ref(v___x_6064_);
                        v___x_6066_ = l_Lean_Expr_headBeta(v_a_6065_);
                        v___x_6067_ = lean_box(0);
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
                        if lean_obj_tag(v___x_6069_) == 0 {
                            lean_dec_ref_known(v___x_6069_, 1);
                            v___x_6070_ = l_Lean_instantiateMVars___at___00Lean_Elab_ConfigEval_evalExprWithElab___at___00__private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabLibrarySearchConfig_evalConfigItem_spec__0_spec__0___redArg(v_a_6027_, v___y_6032_);
                            return v___x_6070_;
                        } else {
                            lean_dec_ref(v_a_6027_);
                            v_a_6071_ = lean_ctor_get(v___x_6069_, 0);
                            v_isSharedCheck_6078_ = (!lean_is_exclusive(v___x_6069_)) as u8;
                            if v_isSharedCheck_6078_ == 0 {
                                v___x_6073_ = v___x_6069_;
                                v_isShared_6074_ = v_isSharedCheck_6078_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_6071_);
                                lean_dec(v___x_6069_);
                                v___x_6073_ = lean_box(0);
                                v_isShared_6074_ = v_isSharedCheck_6078_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_stx_6028_);
                    lean_dec_ref(v_a_6027_);
                    lean_dec_ref(v_expectedType_6026_);
                    v_a_6079_ = lean_ctor_get(v___x_6036_, 0);
                    v_isSharedCheck_6086_ = (!lean_is_exclusive(v___x_6036_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v___x_6081_ = v___x_6036_;
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6079_);
                        lean_dec(v___x_6036_);
                        v___x_6081_ = lean_box(0);
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
                    v_reuseFailAlloc_6051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6051_, 0, v_a_6045_);
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
                    v_reuseFailAlloc_6062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
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
                    v_reuseFailAlloc_6077_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6077_, 0, v_a_6071_);
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
                    v_reuseFailAlloc_6085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_a_6079_);
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
    mut v_snd_6087_: *mut LeanObject,
    mut v___f_6088_: *mut LeanObject,
    mut v___f_6089_: *mut LeanObject,
    mut v___x_6090_: *mut LeanObject,
    mut v___x_6091_: *mut LeanObject,
    mut v___x_6092_: *mut LeanObject,
    mut v_expectedType_6093_: *mut LeanObject,
    mut v_a_6094_: *mut LeanObject,
    mut v_stx_6095_: *mut LeanObject,
    mut v___y_6096_: *mut LeanObject,
    mut v___y_6097_: *mut LeanObject,
    mut v___y_6098_: *mut LeanObject,
    mut v___y_6099_: *mut LeanObject,
    mut v___y_6100_: *mut LeanObject,
    mut v___y_6101_: *mut LeanObject,
    mut v___y_6102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7080__boxed_6103_: u8 = 0;
    let mut v___x_7081__boxed_6104_: u8 = 0;
    let mut v_res_6105_: *mut LeanObject = core::ptr::null_mut();
    v___x_7080__boxed_6103_ = (lean_unbox(v___x_6091_) as u8);
    v___x_7081__boxed_6104_ = (lean_unbox(v___x_6092_) as u8);
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
    lean_dec(v___y_6101_);
    lean_dec_ref(v___y_6100_);
    lean_dec(v___y_6099_);
    lean_dec_ref(v___y_6098_);
    lean_dec(v___y_6097_);
    lean_dec_ref(v___y_6096_);
    return v_res_6105_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__3(
    mut v___f_6106_: *mut LeanObject,
    mut v___f_6107_: *mut LeanObject,
    mut v___x_6108_: u8,
    mut v_stx_6109_: *mut LeanObject,
    mut v_expectedType_6110_: *mut LeanObject,
    mut v___y_6111_: *mut LeanObject,
    mut v___y_6112_: *mut LeanObject,
    mut v___y_6113_: *mut LeanObject,
    mut v___y_6114_: *mut LeanObject,
    mut v___y_6115_: *mut LeanObject,
    mut v___y_6116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6119_: u8 = 0;
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: u8 = 0;
    let mut v___x_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6136_: u8 = 0;
    let mut v___x_6138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_expectedType_6110_);
                v___x_6118_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6118_, 0, v_expectedType_6110_);
                v___x_6119_ = 0;
                v___x_6120_ = lean_box(0);
                v___x_6121_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_6118_,
                    v___x_6119_,
                    v___x_6120_,
                    v___y_6113_,
                    v___y_6114_,
                    v___y_6115_,
                    v___y_6116_,
                );
                if lean_obj_tag(v___x_6121_) == 0 {
                    v_a_6122_ = lean_ctor_get(v___x_6121_, 0);
                    lean_inc(v_a_6122_);
                    lean_dec_ref_known(v___x_6121_, 1);
                    v___x_6123_ = l_Lean_Expr_mvarId_x21(v_a_6122_);
                    v___x_6124_ = l_Lean_MVarId_intros(
                        v___x_6123_,
                        v___y_6113_,
                        v___y_6114_,
                        v___y_6115_,
                        v___y_6116_,
                    );
                    if lean_obj_tag(v___x_6124_) == 0 {
                        v_a_6125_ = lean_ctor_get(v___x_6124_, 0);
                        lean_inc(v_a_6125_);
                        lean_dec_ref_known(v___x_6124_, 1);
                        v_snd_6126_ = lean_ctor_get(v_a_6125_, 1);
                        lean_inc_n(v_snd_6126_, 2);
                        lean_dec(v_a_6125_);
                        v___x_6127_ = lean_unsigned_to_nat(10);
                        v___x_6128_ = 0;
                        v___x_6129_ = lean_box((v___x_6108_) as usize);
                        v___x_6130_ = lean_box((v___x_6128_) as usize);
                        v___f_6131_ = lean_alloc_closure(
                            l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__2___boxed
                                as *mut core::ffi::c_void,
                            16,
                            9,
                        );
                        lean_closure_set(v___f_6131_, 0, v_snd_6126_);
                        lean_closure_set(v___f_6131_, 1, v___f_6106_);
                        lean_closure_set(v___f_6131_, 2, v___f_6107_);
                        lean_closure_set(v___f_6131_, 3, v___x_6127_);
                        lean_closure_set(v___f_6131_, 4, v___x_6129_);
                        lean_closure_set(v___f_6131_, 5, v___x_6130_);
                        lean_closure_set(v___f_6131_, 6, v_expectedType_6110_);
                        lean_closure_set(v___f_6131_, 7, v_a_6122_);
                        lean_closure_set(v___f_6131_, 8, v_stx_6109_);
                        v___x_6132_ = l_Lean_MVarId_withContext___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__2___redArg(v_snd_6126_, v___f_6131_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_);
                        return v___x_6132_;
                    } else {
                        lean_dec(v_a_6122_);
                        lean_dec_ref(v_expectedType_6110_);
                        lean_dec(v_stx_6109_);
                        lean_dec_ref(v___f_6107_);
                        lean_dec_ref(v___f_6106_);
                        v_a_6133_ = lean_ctor_get(v___x_6124_, 0);
                        v_isSharedCheck_6140_ = (!lean_is_exclusive(v___x_6124_)) as u8;
                        if v_isSharedCheck_6140_ == 0 {
                            v___x_6135_ = v___x_6124_;
                            v_isShared_6136_ = v_isSharedCheck_6140_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6133_);
                            lean_dec(v___x_6124_);
                            v___x_6135_ = lean_box(0);
                            v_isShared_6136_ = v_isSharedCheck_6140_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_expectedType_6110_);
                    lean_dec(v_stx_6109_);
                    lean_dec_ref(v___f_6107_);
                    lean_dec_ref(v___f_6106_);
                    return v___x_6121_;
                }
            }
            1 => {
                if v_isShared_6136_ == 0 {
                    v___x_6138_ = v___x_6135_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_a_6133_);
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
    mut v___f_6141_: *mut LeanObject,
    mut v___f_6142_: *mut LeanObject,
    mut v___x_6143_: *mut LeanObject,
    mut v_stx_6144_: *mut LeanObject,
    mut v_expectedType_6145_: *mut LeanObject,
    mut v___y_6146_: *mut LeanObject,
    mut v___y_6147_: *mut LeanObject,
    mut v___y_6148_: *mut LeanObject,
    mut v___y_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7237__boxed_6153_: u8 = 0;
    let mut v_res_6154_: *mut LeanObject = core::ptr::null_mut();
    v___x_7237__boxed_6153_ = (lean_unbox(v___x_6143_) as u8);
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
    lean_dec(v___y_6151_);
    lean_dec_ref(v___y_6150_);
    lean_dec(v___y_6149_);
    lean_dec_ref(v___y_6148_);
    lean_dec(v___y_6147_);
    lean_dec_ref(v___y_6146_);
    return v_res_6154_;
}
pub unsafe fn l_Lean_Elab_LibrarySearch_elabExact_x3fTerm(
    mut v_stx_6162_: *mut LeanObject,
    mut v_expectedType_x3f_6163_: *mut LeanObject,
    mut v_a_6164_: *mut LeanObject,
    mut v_a_6165_: *mut LeanObject,
    mut v_a_6166_: *mut LeanObject,
    mut v_a_6167_: *mut LeanObject,
    mut v_a_6168_: *mut LeanObject,
    mut v_a_6169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: u8 = 0;
    v___x_6171_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1;
    lean_inc(v_stx_6162_);
    v___x_6172_ = l_Lean_Syntax_isOfKind(v_stx_6162_, v___x_6171_);
    if v___x_6172_ == 0 {
        let mut v___x_6173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_expectedType_x3f_6163_);
        lean_dec(v_stx_6162_);
        v___x_6173_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__0___redArg();
        return v___x_6173_;
    } else {
        let mut v___f_6174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6176_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6177_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_6178_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
        v___f_6174_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__2;
        v___x_6175_ = lean_box((v___x_6172_) as usize);
        v___f_6176_ = lean_alloc_closure(
            l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__1___boxed as *mut core::ffi::c_void,
            7,
            1,
        );
        lean_closure_set(v___f_6176_, 0, v___x_6175_);
        v___x_6177_ = lean_box((v___x_6172_) as usize);
        v___f_6178_ = lean_alloc_closure(
            l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___lam__3___boxed as *mut core::ffi::c_void,
            12,
            4,
        );
        lean_closure_set(v___f_6178_, 0, v___f_6174_);
        lean_closure_set(v___f_6178_, 1, v___f_6176_);
        lean_closure_set(v___f_6178_, 2, v___x_6177_);
        lean_closure_set(v___f_6178_, 3, v_stx_6162_);
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
    mut v_stx_6180_: *mut LeanObject,
    mut v_expectedType_x3f_6181_: *mut LeanObject,
    mut v_a_6182_: *mut LeanObject,
    mut v_a_6183_: *mut LeanObject,
    mut v_a_6184_: *mut LeanObject,
    mut v_a_6185_: *mut LeanObject,
    mut v_a_6186_: *mut LeanObject,
    mut v_a_6187_: *mut LeanObject,
    mut v_a_6188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6189_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6187_);
    lean_dec_ref(v_a_6186_);
    lean_dec(v_a_6185_);
    lean_dec_ref(v_a_6184_);
    lean_dec(v_a_6183_);
    lean_dec_ref(v_a_6182_);
    return v_res_6189_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3(
    mut v_ref_6190_: *mut LeanObject,
    mut v_msgData_6191_: *mut LeanObject,
    mut v_severity_6192_: u8,
    mut v_isSilent_6193_: u8,
    mut v___y_6194_: *mut LeanObject,
    mut v___y_6195_: *mut LeanObject,
    mut v___y_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
    mut v___y_6198_: *mut LeanObject,
    mut v___y_6199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6201_: *mut LeanObject = core::ptr::null_mut();
    v___x_6201_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___redArg(v_ref_6190_, v_msgData_6191_, v_severity_6192_, v_isSilent_6193_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_);
    return v___x_6201_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3___boxed(
    mut v_ref_6202_: *mut LeanObject,
    mut v_msgData_6203_: *mut LeanObject,
    mut v_severity_6204_: *mut LeanObject,
    mut v_isSilent_6205_: *mut LeanObject,
    mut v___y_6206_: *mut LeanObject,
    mut v___y_6207_: *mut LeanObject,
    mut v___y_6208_: *mut LeanObject,
    mut v___y_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
    mut v___y_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_6213_: u8 = 0;
    let mut v_isSilent_boxed_6214_: u8 = 0;
    let mut v_res_6215_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_6213_ = (lean_unbox(v_severity_6204_) as u8);
    v_isSilent_boxed_6214_ = (lean_unbox(v_isSilent_6205_) as u8);
    v_res_6215_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logError___at___00Lean_Elab_LibrarySearch_elabExact_x3fTerm_spec__1_spec__1_spec__3(v_ref_6202_, v_msgData_6203_, v_severity_boxed_6213_, v_isSilent_boxed_6214_, v___y_6206_, v___y_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
    lean_dec(v___y_6211_);
    lean_dec_ref(v___y_6210_);
    lean_dec(v___y_6209_);
    lean_dec_ref(v___y_6208_);
    lean_dec(v___y_6207_);
    lean_dec_ref(v___y_6206_);
    lean_dec(v_ref_6202_);
    return v_res_6215_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1()
-> *mut LeanObject {
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut LeanObject = core::ptr::null_mut();
    v___x_6223_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6224_ = l_Lean_Elab_LibrarySearch_elabExact_x3fTerm___closed__1;
    v___x_6225_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1;
    v___x_6226_ = lean_alloc_closure(
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
    mut v_a_6228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6229_: *mut LeanObject = core::ptr::null_mut();
    v_res_6229_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1();
    return v_res_6229_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3()
-> *mut LeanObject {
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    v___x_6256_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1___closed__1;
    v___x_6257_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___closed__6;
    v___x_6258_ = l_Lean_addBuiltinDeclarationRanges(v___x_6256_, v___x_6257_);
    return v___x_6258_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3___boxed(
    mut v_a_6259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6260_: *mut LeanObject = core::ptr::null_mut();
    v_res_6260_ = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3();
    return v_res_6260_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_LibrarySearch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_TryThis(builtin);
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
    l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig = _init_l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig();
    lean_mark_persistent(l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_instEvalExprLibrarySearchConfig);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalExact___regBuiltin_Lean_Elab_LibrarySearch_evalExact_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_evalApply___regBuiltin_Lean_Elab_LibrarySearch_evalApply_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_LibrarySearch_0__Lean_Elab_LibrarySearch_elabExact_x3fTerm___regBuiltin_Lean_Elab_LibrarySearch_elabExact_x3fTerm_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_LibrarySearch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_LibrarySearch(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_LibrarySearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_TryThis(builtin);
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
    res = runtime_initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_LibrarySearch(builtin);
}
